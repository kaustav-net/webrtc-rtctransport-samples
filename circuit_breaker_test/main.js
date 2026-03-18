// ============================================================
// Circuit Breaker Test App – main.js
// One-directional loopback video: sender (transport1) → receiver (transport2)
// Uses WebCodecs + RtcTransport (DTLS-SRTP) with application RTP framing.
// ============================================================

// --------------- Configuration ---------------
const config = {
  iceServers: [{ urls: "stun:stun.l.google.com:19302" }],
  video: {
    width: 640,
    height: 480,
    bitrate: 2_000_000, // bps
    framerate: 30,
  },
  codec: "vp8",
  maxPacketSize: 1200,
};

// --------------- RTP constants ---------------
const RTP_HEADER_SIZE = 12;
const PAYLOAD_DESC_SIZE = 10; // streamVersion(1) + isKey(1) + frameId(2) + packetSeq(1) + numPackets(1) + timestamp(4)
const TOTAL_HEADER_SIZE = RTP_HEADER_SIZE + PAYLOAD_DESC_SIZE;
const RTP_VERSION = 2;
const RTP_PAYLOAD_TYPE = 1;
const RTP_SSRC = 0x12345678;

// --------------- State ---------------
let senderTransport = null;
let receiverTransport = null;
let encoder = null;
let decoder = null;
let mediaStream = null;
let mediaTrack = null;
let frameReader = null;
let sending = false;
let streamVersion = 0;
let rtpSequenceNumber = 0;
let frameId = 0;

// Reassembly
const reassemblyBuffer = {};
const pendingPackets = [];

// BYOB support detection (deferred until transports exist)
let byobSupport = false;
const BUFFER_POOL_SIZE = 100;
let bufferPool = [];

// --------------- Stats counters ---------------
const stats = {
  encFrames: 0,
  encDropped: 0,
  encBytes: 0,
  pktSent: 0,
  bytesSent: 0,
  pktRecv: 0,
  bytesRecv: 0,
  decFrames: 0,
  decLost: 0,
  rtcpCount: 0,
  // Per-second snapshots for rate computation
  _prevEncBytes: 0,
  _prevSentBytes: 0,
  _prevRecvBytes: 0,
  _prevEncFrames: 0,
  _prevDecFrames: 0,
  _prevTime: 0,
};

// --------------- DOM elements ---------------
const eventLogEl = document.getElementById("eventLog");
const errorEl = document.getElementById("error");
const startBtn = document.getElementById("startBtn");
const stopBtn = document.getElementById("stopBtn");
const applyBtn = document.getElementById("applyBtn");
const resolutionSel = document.getElementById("resolution");
const bitrateInput = document.getElementById("bitrateInput");
const fpsInput = document.getElementById("fpsInput");
const cbStatusEl = document.getElementById("cbStatus");
const receiverCanvas = document.getElementById("receiverCanvas");
const senderPreview = document.getElementById("senderPreview");

// Stat value elements
const elEncRes = document.getElementById("encRes");
const elEncFps = document.getElementById("encFps");
const elEncBitrate = document.getElementById("encBitrate");
const elEncFrames = document.getElementById("encFrames");
const elEncDropped = document.getElementById("encDropped");
const elPktSent = document.getElementById("pktSent");
const elBytesSent = document.getElementById("bytesSent");
const elSendBitrate = document.getElementById("sendBitrate");
const elPktDroppedCb = document.getElementById("pktDroppedCb");
const elPktRecv = document.getElementById("pktRecv");
const elBytesRecv = document.getElementById("bytesRecv");
const elRecvBitrate = document.getElementById("recvBitrate");
const elRtcpCount = document.getElementById("rtcpCount");
const elDecRes = document.getElementById("decRes");
const elDecFps = document.getElementById("decFps");
const elDecFrames = document.getElementById("decFrames");
const elDecLost = document.getElementById("decLost");

// --------------- Helpers ---------------
function log(msg) {
  const ts = new Date().toLocaleTimeString();
  eventLogEl.appendChild(document.createTextNode(`[${ts}] ${msg}\n`));
  eventLogEl.scrollTop = eventLogEl.scrollHeight;
}

function logError(msg) {
  errorEl.textContent += msg + "\n";
  log(`ERROR: ${msg}`);
}

function cbLog(msg) {
  const ts = new Date().toLocaleTimeString();
  const span = document.createElement("span");
  span.className = "log-cb";
  span.textContent = `[${ts}] CB: ${msg}\n`;
  eventLogEl.appendChild(span);
  eventLogEl.scrollTop = eventLogEl.scrollHeight;
}

function updateCbStatusUI(state) {
  cbStatusEl.textContent = state.toUpperCase();
  cbStatusEl.className = "cb-status cb-" + state;
}

function updateCbTimerHint(state) {
  const hintEl = document.getElementById("cbTimerHint");
  if (!hintEl) return;
  switch (state) {
    case "closed":
      hintEl.textContent = "";
      break;
    case "open":
      hintEl.textContent = "\u23f3 Open timeout running (5\u201360 s) \u2192 Half-Open";
      break;
    case "half-open":
      hintEl.textContent = "\u23f3 Half-Open probe (3 s) \u2014 re-trips if send bitrate > BWE";
      break;
  }
}

function formatKbps(bitsPerSec) {
  return (bitsPerSec / 1000).toFixed(0) + " kbps";
}

// --------------- Transport setup ---------------
function createRtcTransport(name, isControlling) {
  return new RtcTransport({
    name,
    iceServers: config.iceServers,
    iceControlling: isControlling,
    wireProtocol: "dtls-srtp",
  });
}

function sendCandidateToPeer(peerTransport, event) {
  if (event.candidate) {    
    log(`Sending candidate to peer transport`);
    peerTransport.addRemoteCandidate(event.candidate);
  }
}

async function waitForWritable(transport, name) {
  const hasEvent = "onwritablechange" in RtcTransport.prototype;
  if (hasEvent) {
    await new Promise((resolve) => {
      transport.onwritablechange = async () => {
        if (await transport.writable()) resolve();
      };
    });
    transport.onwritablechange = null;
  } else {
    while (!(await transport.writable())) {
      await new Promise((r) => setTimeout(r, 100));
    }
  }
  log(`${name} is writable`);
}

// --------------- RTP packetisation ---------------
function packetiseAndSend(chunk) {
  const chunkData = new Uint8Array(chunk.byteLength);
  chunk.copyTo(chunkData);

  stats.encFrames++;
  stats.encBytes += chunk.byteLength;

  const maxPayload = config.maxPacketSize - TOTAL_HEADER_SIZE;
  const numPackets = Math.ceil(chunkData.byteLength / maxPayload);
  const packets = [];
  const isKey = chunk.type === "key";
  const ts = chunk.timestamp >>> 0; // ensure unsigned 32-bit

  for (let i = 0, seq = 0; i < chunkData.byteLength; i += maxPayload, seq++) {
    const end = Math.min(i + maxPayload, chunkData.byteLength);
    const pktLen = (end - i) + TOTAL_HEADER_SIZE;

    let buf;
    if (byobSupport) {
      buf = bufferPool.pop();
      if (!buf || buf.byteLength < pktLen) buf = new ArrayBuffer(pktLen);
    } else {
      buf = new ArrayBuffer(pktLen);
    }
    const dv = new DataView(buf, 0, pktLen);

    // RTP header
    const isLastPacket = (seq === numPackets - 1);
    dv.setUint8(0, (RTP_VERSION << 6));
    dv.setUint8(1, (isLastPacket ? 0x80 : 0x00) | (RTP_PAYLOAD_TYPE & 0x7F)); // marker bit on last packet of frame
    dv.setUint16(2, rtpSequenceNumber & 0xFFFF, false);
    rtpSequenceNumber++;
    dv.setUint32(4, ts, false);
    dv.setUint32(8, RTP_SSRC, false);

    // Payload descriptor
    const pd = RTP_HEADER_SIZE;
    dv.setUint8(pd + 0, streamVersion & 0xFF);
    dv.setUint8(pd + 1, isKey ? 1 : 0);
    dv.setUint16(pd + 2, frameId & 0xFFFF, false);
    dv.setUint8(pd + 4, seq);
    dv.setUint8(pd + 5, numPackets);
    dv.setUint32(pd + 6, ts, false);

    // Copy payload
    new Uint8Array(buf, TOTAL_HEADER_SIZE, end - i).set(chunkData.subarray(i, end));

    stats.pktSent++;
    stats.bytesSent += pktLen;

    if (byobSupport) {
      packets.push({ data: new DataView(buf, 0, pktLen) });
    } else {
      packets.push({ data: buf });
    }
  }

  senderTransport.sendPackets(packets);

  // Return buffers to pool
  if (byobSupport) {
    for (const p of packets) {
      bufferPool.push(p.data.buffer);
    }
  }

  frameId++;
}

// --------------- Encoder ---------------
function createEncoder() {
  const enc = new VideoEncoder({
    output: (chunk) => {
      if (!sending) return;
      packetiseAndSend(chunk);
    },
    error: (e) => console.error("Encoder error:", e.message),
  });
  enc.configure({
    codec: config.codec,
    width: config.video.width,
    height: config.video.height,
    bitrate: config.video.bitrate,
    framerate: config.video.framerate,
  });
  return enc;
}

// --------------- Decoder ---------------
function createDecoder() {
  const dec = new VideoDecoder({
    output: (frame) => {
      stats.decFrames++;
      const ctx = receiverCanvas.getContext("2d");
      ctx.drawImage(frame, 0, 0, receiverCanvas.width, receiverCanvas.height);
      frame.close();
    },
    error: (e) => console.error("Decoder error:", e.message),
  });
  dec.configure({
    codec: config.codec,
    codedWidth: config.video.width,
    codedHeight: config.video.height,
  });
  return dec;
}

// --------------- Packet reassembly & decode ---------------
function processReceivedPackets(packets) {
  for (const packet of packets) {
    let data;
    if (byobSupport) {
      let buf = bufferPool.pop();
      if (!buf) buf = new ArrayBuffer(config.maxPacketSize + 16);
      packet.copyPayloadTo(buf);
      data = new Uint8Array(buf, 0, packet.payloadByteLength);
    } else {
      data = new Uint8Array(packet.data);
    }

    stats.pktRecv++;
    stats.bytesRecv += data.byteLength;

    const dv = new DataView(data.buffer, data.byteOffset, data.byteLength);

    // Check if RTCP (payload type byte 200-206)
    if (data.byteLength >= 2) {
      const pt = dv.getUint8(1) & 0x7F;
      // RTCP packet types: SR=200, RR=201, SDES=202, BYE=203, APP=204, RTPFB=205, PSFB=206
      const fullPt = dv.getUint8(1);
      if (fullPt >= 200 && fullPt <= 206) {
        stats.rtcpCount++;
        if (byobSupport) bufferPool.push(data.buffer);
        continue;
      }
    }

    // Must have at least the full header
    if (data.byteLength < TOTAL_HEADER_SIZE) {
      if (byobSupport) bufferPool.push(data.buffer);
      continue;
    }

    const version = dv.getUint8(RTP_HEADER_SIZE);
    if (version !== (streamVersion & 0xFF)) {
      // Old stream, discard
      if (byobSupport) bufferPool.push(data.buffer);
      continue;
    }

    const isKey = dv.getUint8(RTP_HEADER_SIZE + 1) === 1;
    const fid = dv.getUint16(RTP_HEADER_SIZE + 2, false);
    const pktSeq = dv.getUint8(RTP_HEADER_SIZE + 4);
    const numPkts = dv.getUint8(RTP_HEADER_SIZE + 5);
    const timestamp = dv.getUint32(RTP_HEADER_SIZE + 6, false);
    const payload = new Uint8Array(data.buffer, data.byteOffset + TOTAL_HEADER_SIZE,
                                   data.byteLength - TOTAL_HEADER_SIZE);

    if (!reassemblyBuffer[fid]) {
      reassemblyBuffer[fid] = {
        packets: new Array(numPkts),
        numPackets: numPkts,
        isKeyFrame: isKey,
        receivedCount: 0,
        timestamp,
        arrivalTime: performance.now(),
      };
    }
    const entry = reassemblyBuffer[fid];
    if (!entry.packets[pktSeq]) {
      entry.receivedCount++;
    }
    // Make a copy of payload so we can return buffer to pool
    entry.packets[pktSeq] = payload.slice();

    if (byobSupport) bufferPool.push(data.buffer);

    if (entry.receivedCount === entry.numPackets) {
      // Reassemble
      const totalSize = entry.packets.reduce((a, p) => a + p.byteLength, 0);
      const frame = new Uint8Array(totalSize);
      let off = 0;
      for (const p of entry.packets) {
        frame.set(p, off);
        off += p.byteLength;
      }
      try {
        decoder.decode(new EncodedVideoChunk({
          timestamp: entry.timestamp,
          type: entry.isKeyFrame ? "key" : "delta",
          data: frame,
        }));
      } catch (e) {
        console.warn("Decode error:", e);
      }
      delete reassemblyBuffer[fid];
    }
  }

  // Expire incomplete frames older than 2 seconds
  const now = performance.now();
  for (const fid of Object.keys(reassemblyBuffer)) {
    if (now - reassemblyBuffer[fid].arrivalTime > 2000) {
      stats.decLost++;
      delete reassemblyBuffer[fid];
    }
  }
}

// --------------- Receive polling ---------------
async function pollReceiver(transport, callback) {
  while (true) {
    const packets = transport.getReceivedPackets();
    if (packets.length > 0) callback(packets);
    await new Promise((r) => setTimeout(r, 5));
  }
}

// --------------- Stats update ---------------
function updateStats() {
  const now = performance.now();
  const dt = (now - stats._prevTime) / 1000;
  if (dt <= 0) {
    stats._prevTime = now;
    return;
  }

  const encFps = (stats.encFrames - stats._prevEncFrames) / dt;
  const decFps = (stats.decFrames - stats._prevDecFrames) / dt;
  const encBitrate = ((stats.encBytes - stats._prevEncBytes) * 8) / dt;
  const sendBitrate = ((stats.bytesSent - stats._prevSentBytes) * 8) / dt;
  const recvBitrate = ((stats.bytesRecv - stats._prevRecvBytes) * 8) / dt;

  elEncRes.textContent = `${config.video.width}x${config.video.height}`;
  elEncFps.textContent = encFps.toFixed(1);
  elEncBitrate.textContent = formatKbps(encBitrate);
  elEncFrames.textContent = stats.encFrames;
  elEncDropped.textContent = stats.encDropped;

  elPktSent.textContent = stats.pktSent;
  elBytesSent.textContent = stats.bytesSent;
  elSendBitrate.textContent = formatKbps(sendBitrate);

  // Circuit breaker drops are not directly counted by JS—shown as N/A
  // (the transport drops them internally in kOpen state)
  if (senderTransport) {
    const cbState = senderTransport.circuitBreakerState;
    if (cbState === "open") {
      elPktDroppedCb.textContent = "Active (dropping)";
    } else if (cbState === "half-open") {
      elPktDroppedCb.textContent = "Probing (half-open)";
    } else {
      elPktDroppedCb.textContent = "0";
    }
  }

  elPktRecv.textContent = stats.pktRecv;
  elBytesRecv.textContent = stats.bytesRecv;
  elRecvBitrate.textContent = formatKbps(recvBitrate);
  elRtcpCount.textContent = stats.rtcpCount;

  elDecRes.textContent = `${config.video.width}x${config.video.height}`;
  elDecFps.textContent = decFps.toFixed(1);
  elDecFrames.textContent = stats.decFrames;
  elDecLost.textContent = stats.decLost;

  stats._prevEncBytes = stats.encBytes;
  stats._prevSentBytes = stats.bytesSent;
  stats._prevRecvBytes = stats.bytesRecv;
  stats._prevEncFrames = stats.encFrames;
  stats._prevDecFrames = stats.decFrames;
  stats._prevTime = now;
}

// --------------- Camera acquisition ---------------
async function acquireCamera() {
  if (mediaTrack) {
    // Camera already acquired — just apply new constraints
    await mediaTrack.applyConstraints({
      width: { ideal: config.video.width },
      height: { ideal: config.video.height },
      frameRate: { ideal: config.video.framerate },
    });
    return;
  }
  mediaStream = await navigator.mediaDevices.getUserMedia({
    video: {
      width: { ideal: config.video.width },
      height: { ideal: config.video.height },
      frameRate: { ideal: config.video.framerate },
    },
  });
  mediaTrack = mediaStream.getVideoTracks()[0];
  senderPreview.srcObject = mediaStream;
}

// --------------- Encode loop ---------------
async function startEncodeLoop() {
  // Create encoder
  frameId = 0;
  if (encoder) {
    try { encoder.close(); } catch (_) {}
  }
  encoder = createEncoder();

  // Read frames via MediaStreamTrackProcessor
  const processor = new MediaStreamTrackProcessor(mediaTrack);
  frameReader = processor.readable.getReader();

  let isFirstFrame = true;
  try {
    while (sending) {
      const { value: frame, done } = await frameReader.read();
      if (done || !sending) {
        if (frame) frame.close();
        break;
      }
      if (encoder.encodeQueueSize > 2) {
        frame.close();
        stats.encDropped++;
      } else {
        const keyFrame = isFirstFrame || (stats.encFrames % 150 === 0);
        isFirstFrame = false;
        encoder.encode(frame, { keyFrame });
        frame.close();
      }
    }
  } catch (e) {
    if (sending) console.error("Frame read error:", e);
  }
}

function stopEncodeLoop() {
  sending = false;
  if (frameReader) {
    try { frameReader.cancel(); } catch (_) {}
    frameReader = null;
  }
  if (encoder) {
    try { encoder.close(); } catch (_) {}
    encoder = null;
  }
}

// --------------- Start / stop video ---------------
async function startVideoLoop() {
  sending = true;
  await acquireCamera();
  await startEncodeLoop();
}

function stopVideoLoop() {
  stopEncodeLoop();
  // Release camera and preview
  if (mediaTrack) {
    mediaTrack.stop();
    mediaTrack = null;
    mediaStream = null;
  }
  senderPreview.srcObject = null;
}

// --------------- Apply config ---------------
function applyConfig() {
  const [w, h] = resolutionSel.value.split("x").map(Number);
  const br = parseInt(bitrateInput.value, 10) * 1000; // kbps → bps
  const fps = parseInt(fpsInput.value, 10);

  config.video.width = w;
  config.video.height = h;
  config.video.bitrate = br;
  config.video.framerate = fps;

  streamVersion++;

  // Reset decoder
  if (decoder) {
    try { decoder.close(); } catch (_) {}
  }
  decoder = createDecoder();

  // Clear reassembly
  for (const k of Object.keys(reassemblyBuffer)) delete reassemblyBuffer[k];
  pendingPackets.length = 0;

  log(`Config applied: ${w}x${h} @ ${fps}fps, ${bitrateInput.value} kbps`);

  // If currently sending, restart encode loop with new config (keep camera)
  if (sending) {
    stopEncodeLoop();
    sending = true;
    acquireCamera()
      .then(() => startEncodeLoop())
      .catch((e) => logError("Restart error: " + e.message));
  }
}

// --------------- Circuit breaker event handlers ---------------
function setupCircuitBreakerListeners(transport) {
  transport.oncircuitbreakerstatechange = (event) => {
    const state = event.state; // "closed", "open", or "half-open"
    updateCbStatusUI(state);
    updateCbTimerHint(state);
    switch (state) {
      case "open":
        cbLog("STATE \u2192 OPEN: circuit breaker tripped, packets being dropped!");
        break;
      case "half-open":
        cbLog("STATE \u2192 HALF-OPEN: probe window, packets flowing for evaluation");
        break;
      case "closed":
        cbLog("STATE \u2192 CLOSED: circuit breaker recovered, sending resumed");
        break;
    }
  };
  transport.oncircuitbreakeroverusewarning = () => {
    cbLog("OVERUSE WARNING: sender bitrate exceeding estimated bandwidth");
  };
}

// --------------- Initialization ---------------
async function main() {
  if (!window.RtcTransport) {
    logError("RtcTransport not supported. Run Chromium with --enable-blink-features=RTCRtpTransport");
    return;
  }

  byobSupport = typeof RtcReceivedPacket !== "undefined" &&
                RtcReceivedPacket &&
                "copyPayloadTo" in RtcReceivedPacket.prototype;
  if (byobSupport) {
    bufferPool = Array.from({ length: BUFFER_POOL_SIZE },
      () => new ArrayBuffer(config.maxPacketSize + 16));
  }
  log(byobSupport ? "BYOB support detected" : "No BYOB support");

  // Create transports: sender (transport1) → receiver (transport2)
  senderTransport = createRtcTransport("sender", true);
  receiverTransport = createRtcTransport("receiver", false);

  // ICE candidate exchange
  senderTransport.onicecandidate = (e) => sendCandidateToPeer(receiverTransport, e);
  receiverTransport.onicecandidate = (e) => sendCandidateToPeer(senderTransport, e);

  // DTLS parameter exchange
  receiverTransport.setRemoteDtlsParameters({
    sslRole: "server",
    fingerprintDigestAlgorithm: senderTransport.fingerprintDigestAlgorithm,
    fingerprint: senderTransport.fingerprint,
  });
  senderTransport.setRemoteDtlsParameters({
    sslRole: "client",
    fingerprintDigestAlgorithm: receiverTransport.fingerprintDigestAlgorithm,
    fingerprint: receiverTransport.fingerprint,
  });

  // Circuit breaker listeners on sender
  setupCircuitBreakerListeners(senderTransport);
  updateCbStatusUI(senderTransport.circuitBreakerState || "closed");

  // Decoder
  decoder = createDecoder();

  // Wait for both transports to be writable
  log("Waiting for transports to become writable...");
  await Promise.all([
    waitForWritable(senderTransport, "sender"),
    waitForWritable(receiverTransport, "receiver"),
  ]);

  log("Transports ready");

  // Poll receiver side (transport2) for RTP packets from sender
  // The receiver gets the sent RTP video packets
  pollReceiver(receiverTransport, (packets) => processReceivedPackets(packets));

  // Also poll sender side for any RTCP coming back from receiver
  // (RFC 8888 congestion control feedback is generated by the transport internally,
  //  but any RTCP that isn't consumed internally gets forwarded to the app)
  pollReceiver(senderTransport, (packets) => {
    for (const pkt of packets) {
      let data;
      if (byobSupport) {
        let buf = bufferPool.pop();
        if (!buf) buf = new ArrayBuffer(config.maxPacketSize + 16);
        pkt.copyPayloadTo(buf);
        data = new Uint8Array(buf, 0, pkt.payloadByteLength);
      } else {
        data = new Uint8Array(pkt.data);
      }
      // Count any RTCP we see on the sender side
      if (data.byteLength >= 2) {
        const pt = data[1];
        if (pt >= 200 && pt <= 206) {
          stats.rtcpCount++;
        }
      }
      if (byobSupport && data.buffer) bufferPool.push(data.buffer);
    }
  });

  // Enable buttons
  startBtn.disabled = false;
  startBtn.onclick = () => {
    startBtn.disabled = true;
    stopBtn.disabled = false;
    startVideoLoop().catch((e) => logError("Start error: " + e.message));
  };
  stopBtn.onclick = () => {
    stopBtn.disabled = true;
    startBtn.disabled = false;
    stopVideoLoop();
  };
  applyBtn.onclick = () => applyConfig();

  // Stats refresh
  stats._prevTime = performance.now();
  setInterval(updateStats, 1000);
}

main();
