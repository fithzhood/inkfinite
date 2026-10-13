'use strict';

// Inside the Capacitor APK (it loads this page from GitHub Pages)
if (window.Capacitor && window.Capacitor.isNativePlatform && window.Capacitor.isNativePlatform()) document.body.classList.add('capacitor');

// ─── Constants ───────────────────────────────────────────────────────────────
const WIDTH_STEPS    = [1, 2, 3, 5, 8, 12, 20, 32];   // pencil / laser
const HL_WIDTH_STEPS = [8, 12, 20, 32, 45, 60, 80];   // highlighter only
const TEXT_SIZES     = [10, 14, 18, 24, 32, 48, 64, 96]; // text tool font sizes (world px)
const GRID_SIZE   = 40;
const LASER_TTL   = 1500;
const MAX_TABS    = 9;
const MAX_CUSTOM  = 5;
const DBL_TAP_MS  = 400;

const HALF_GRID   = GRID_SIZE / 2;  // 20px snap for shapes
const SHAPE_TOOLS  = new Set(['line','dashedLine','arrow','rect','square','roundedRect','circle','ellipse','goniometric','regularPolygon','rightTriangle','polygon','cartesian','cartesianQ1','cartesianQ12']);
const ERASER_TOOLS = new Set(['pointEraser','lassoEraser']);
const EDGE_ZONE      = 60;   // px from edge to start auto-scroll
const EDGE_MAX_SPEED = 14;   // max scroll pixels/frame
const TAP_HIT_R      = 14;   // touch hit radius (screen px)
let   shapeIdSeq  = 0;

const DARK_PALETTE  = ['#FFFFFF','#FF4444','#55BBFF','#88FF88','#FFEE44','#FF44FF'];
const LIGHT_PALETTE = ['#111111','#CC0000','#0055AA','#228822','#AA8800','#990099'];
const HL_PALETTE    = ['#FFF000','#4DFFF3','#FF66B2','#66FF88','#FF9900'];

// ─── Tab state ───────────────────────────────────────────────────────────────
function makeTab() {
  return {
    bgColor: '#000000', gridEnabled: false,
    strokes: [], highlighters: [],
    undoStack: [], redoStack: [],
    transform: { scale: 1, tx: 0, ty: 0 },
    toolWidths: { pencil: 3, highlighter: 5, laser: 2, shape: 3, text: 6 },
    toolWidthPx: { pencil: 5, highlighter: 60, laser: 3, shape: 5, text: 64 },
    seq: 0,
    shapes: [],
  };
}
const state = {
  tabs: [makeTab()], activeTabIndex: 0,
  activeTool: 'pencil',
  activeColor: '#FFFFFF', highlighterColor: '#FFF000',
  customColors: [],
  dirty: true, laser: null,
  straighten: false,
};

// Shape drawing state
const ss = {
  drawing: false,
  preview: null,   // shape object being previewed
  startPt: null,   // world-space drag start
  polyVerts: [],        // accumulated vertices for freehand polygon
  regularPolySides: 3,  // sides for regularPolygon tool
  lastPointerScreen: null,
};

// Selection tool state
const sel = {
  phase: 'idle', // 'idle'|'lasso'|'selected'|'dragging'|'resizing'|'rotating'|'vertex'
  lassoPoints: [],
  items: null,         // { strokes:[], highlighters:[], shapes:[] }
  bbox: null,          // { x, y, w, h } world space
  dragHandle: null,    // 'move' | 'tl'|'tr'|'bl'|'br'|'tm'|'bm'|'lm'|'rm'|'rotate'
  dragStartScreen: null,
  dragStartWorld: null,
  origData: null,
  origBbox: null,
  clipboard: null,
  vertHandle: null,    // handle id when phase==='vertex'
  vertOrigShape: null, // deep clone of shape at vertex-drag start
};

// Edge-scroll state (shared between lasso-select and touch-select)
const edgeScroll = { vx: 0, vy: 0 };
let lastDragScreen = null;

// Touch-select state
let touchPan = false, touchPanTx0 = 0, touchPanTy0 = 0, touchPanScreen0 = null;
let touchTapScreen = null;

function tab() { return state.tabs[state.activeTabIndex]; }

// ─── Canvas ──────────────────────────────────────────────────────────────────
const canvas = document.getElementById('canvas');
let ctx      = canvas.getContext('2d');
function resizeCanvas() {
  canvas.width = window.innerWidth; canvas.height = window.innerHeight;
  state.dirty = true;
}
window.addEventListener('resize', () => { resizeCanvas(); repositionPanels(); });
resizeCanvas();

// ─── Coords ──────────────────────────────────────────────────────────────────
function toWorld(sx, sy) {
  const t = tab().transform;
  return { x: (sx - t.tx) / t.scale, y: (sy - t.ty) / t.scale };
}

function worldToScreen(wx, wy) {
  const t = tab().transform;
  return { x: wx * t.scale + t.tx, y: wy * t.scale + t.ty };
}
function snapHG(p) {
  return { x: Math.round(p.x / HALF_GRID) * HALF_GRID, y: Math.round(p.y / HALF_GRID) * HALF_GRID };
}
function snapGrid(p) {
  return { x: Math.round(p.x / GRID_SIZE) * GRID_SIZE, y: Math.round(p.y / GRID_SIZE) * GRID_SIZE };
}

// All goniometric circle angles (30° and 45° multiples)
const GONIO_ANGLES = [...new Set([...Array.from({length:12},(_,i)=>i*30), ...Array.from({length:8},(_,i)=>i*45)])];

function snapToGoniometric(screenX, screenY) {
  const SNAP_R = 18; // screen-space pixels
  let best = null, bestDist = SNAP_R;
  for (const shape of tab().shapes) {
    if (shape.type !== 'goniometric') continue;
    const r = Math.hypot(shape.rp.x - shape.cx, shape.rp.y - shape.cy);
    for (const deg of GONIO_ANGLES) {
      const rad = deg * Math.PI / 180;
      const wx = shape.cx + r * Math.cos(rad);
      const wy = shape.cy - r * Math.sin(rad); // math convention: +Y = up = -screen Y
      const sp = worldToScreen(wx, wy);
      const d = Math.hypot(screenX - sp.x, screenY - sp.y);
      if (d < bestDist) { bestDist = d; best = { x: wx, y: wy }; }
    }
  }
  return best;
}
function straightenEnd(start, end) {
  const dx = end.x - start.x, dy = end.y - start.y;
  const angle = Math.atan2(dy, dx);
  const snapped = Math.round(angle / (Math.PI / 4)) * (Math.PI / 4);
  const dist = Math.hypot(dx, dy);
  return { x: start.x + Math.cos(snapped) * dist, y: start.y + Math.sin(snapped) * dist };
}
function shapeStrokeWidth() {
  return getRawWidth('shape');
}

// ─── Colour helpers ──────────────────────────────────────────────────────────
function hexToRgb(h) { return { r:parseInt(h.slice(1,3),16), g:parseInt(h.slice(3,5),16), b:parseInt(h.slice(5,7),16) }; }
function luminance(h) {
  const {r,g,b} = hexToRgb(h);
  const l = v => { v/=255; return v<=0.04045?v/12.92:Math.pow((v+0.055)/1.055,2.4); };
  return 0.2126*l(r)+0.7152*l(g)+0.0722*l(b);
}
function hexToHsl(h) {
  let {r,g,b} = hexToRgb(h); r/=255;g/=255;b/=255;
  const max=Math.max(r,g,b),min=Math.min(r,g,b);
  let hh,s,l=(max+min)/2;
  if(max===min){hh=s=0;}else{
    const d=max-min; s=l>0.5?d/(2-max-min):d/(max+min);
    switch(max){case r:hh=(g-b)/d+(g<b?6:0);break;case g:hh=(b-r)/d+2;break;default:hh=(r-g)/d+4;}
    hh/=6;
  }
  return {h:hh*360,s:s*100,l:l*100};
}
function hslToHex(h,s,l) {
  s/=100;l/=100; const a=s*Math.min(l,1-l);
  const f=n=>{const k=(n+h/30)%12;const c=l-a*Math.max(-1,Math.min(k-3,9-k,1));return Math.round(255*c).toString(16).padStart(2,'0');};
  return '#'+f(0)+f(8)+f(4);
}

// ─── Rendering ───────────────────────────────────────────────────────────────
function drawGrid(t) {
  const {scale,tx,ty} = t.transform;
  ctx.strokeStyle = luminance(t.bgColor)>0.5?'rgba(0,0,0,0.15)':'rgba(255,255,255,0.15)';
  ctx.lineWidth = 1/scale;
  const left=-tx/scale, top=-ty/scale;
  const right=(canvas.width-tx)/scale, bottom=(canvas.height-ty)/scale;
  const sx=Math.floor(left/GRID_SIZE)*GRID_SIZE, sy=Math.floor(top/GRID_SIZE)*GRID_SIZE;
  ctx.beginPath();
  for(let x=sx;x<=right;x+=GRID_SIZE){ctx.moveTo(x,top);ctx.lineTo(x,bottom);}
  for(let y=sy;y<=bottom;y+=GRID_SIZE){ctx.moveTo(left,y);ctx.lineTo(right,y);}
  ctx.stroke();
}

// Chaikin subdivision — smooths a polyline by replacing each segment with
// two new points at 1/4 and 3/4 of the segment. Width array is co-interpolated.
function chaikinSmooth(pts, widths, iters) {
  let p = pts, w = widths;
  for (let k = 0; k < iters; k++) {
    const np = [p[0]], nw = w ? [w[0]] : null;
    for (let i = 0; i < p.length - 1; i++) {
      const p0 = p[i], p1 = p[i + 1];
      np.push({ x: 0.75*p0.x + 0.25*p1.x, y: 0.75*p0.y + 0.25*p1.y });
      np.push({ x: 0.25*p0.x + 0.75*p1.x, y: 0.25*p0.y + 0.75*p1.y });
      if (nw) {
        const w0 = w[i], w1 = w[i + 1] ?? w[i];
        nw.push(0.75*w0 + 0.25*w1);
        nw.push(0.25*w0 + 0.75*w1);
      }
    }
    np.push(p[p.length - 1]);
    if (nw) nw.push(w[w.length - 1]);
    p = np; w = nw;
  }
  return { pts: p, widths: w };
}

function catmull(pts, tension, out = ctx) {
  if(pts.length<2) return;
  if(pts.length===2){out.moveTo(pts[0].x,pts[0].y);out.lineTo(pts[1].x,pts[1].y);return;}
  out.moveTo(pts[0].x,pts[0].y);
  for(let i=0;i<pts.length-1;i++){
    const p0=pts[Math.max(0,i-1)],p1=pts[i],p2=pts[i+1],p3=pts[Math.min(pts.length-1,i+2)];
    out.bezierCurveTo(
      p1.x+(p2.x-p0.x)*tension/3, p1.y+(p2.y-p0.y)*tension/3,
      p2.x-(p3.x-p1.x)*tension/3, p2.y-(p3.y-p1.y)*tension/3,
      p2.x, p2.y
    );
  }
}

// Stroke geometry cache — a finished stroke is smoothed once into a few Path2D runs
// (plus its world bbox) and reused every frame. Edits that move points in place
// must call itemsChanged() so the cache and the baked layer are rebuilt.
const geomCache = new WeakMap();
function buildStrokeGeom(s) {
  let x0=Infinity,y0=Infinity,x1=-Infinity,y1=-Infinity,maxW=s.width||1;
  for(const p of s.points){ if(p.x<x0)x0=p.x; if(p.x>x1)x1=p.x; if(p.y<y0)y0=p.y; if(p.y>y1)y1=p.y; }
  const runs=[];
  if(s.widths&&s.widths.length>1&&!s.alpha){
    // Variable-width (pressure) for pencil only — Chaikin-smoothed. Consecutive segments
    // whose width rounds to the same step share one path: a handful of stroke() calls
    // per stroke instead of one per segment.
    const sm=chaikinSmooth(s.points, s.widths, 3);
    const q=Math.max(0.05,(s.width||1)*0.04);
    let path=null, runK=null;
    for(let i=0;i<sm.pts.length-1;i++){
      const a=sm.pts[i],b=sm.pts[i+1];
      const k=Math.round(((sm.widths[i]+(sm.widths[i+1]??sm.widths[i]))/2)/q);
      if(k!==runK){
        const w=Math.max(0.5,k*q);
        path=new Path2D(); path.moveTo(a.x,a.y); runs.push({path,w}); runK=k;
        if(w>maxW) maxW=w;
      }
      path.lineTo(b.x,b.y);
    }
  } else {
    // Single-path stroke (highlighter and uniform)
    const path=new Path2D(); catmull(s.points,s.tension||0.5,path);
    runs.push({path,w:Math.max(0.5,s.width||1)});
  }
  const pad=maxW; // half the width, doubled for catmull overshoot
  return { runs, pts:s.points, n:s.points.length, w:s.width,
           bbox:{x0:x0-pad,y0:y0-pad,x1:x1+pad,y1:y1+pad} };
}
function strokeGeom(s) {
  let g=geomCache.get(s);
  if(!g||g.pts!==s.points||g.n!==s.points.length||g.w!==s.width){
    g=buildStrokeGeom(s);
    if(s!==curStroke) geomCache.set(s,g); // the live stroke changes every frame
  }
  return g;
}
// Call after editing items in place (selection move/resize/rotate, vertex drag, text).
let sceneVer=0;
function itemsChanged(items) {
  if(items){ items.strokes.forEach(s=>geomCache.delete(s)); items.highlighters.forEach(s=>geomCache.delete(s)); }
  sceneVer++;
}

function drawStroke(s) {
  if(!s.points.length) return;
  ctx.save();
  ctx.globalAlpha = s.alpha ?? 1;
  ctx.lineCap='round'; ctx.lineJoin='round';
  if(s.points.length===1){
    ctx.beginPath(); ctx.arc(s.points[0].x,s.points[0].y,(s.width||1)/2,0,Math.PI*2);
    ctx.fillStyle=s.color; ctx.fill(); ctx.restore(); return;
  }
  ctx.strokeStyle=s.color;
  // The old per-segment drawing piled up antialiasing at the edges, so lines read
  // about 0.6 screen px bolder than one clean path; keep that look (not for the
  // translucent highlighter, which was a single path already).
  const bold=s.alpha?0:0.6/ctx.getTransform().a;
  for(const r of strokeGeom(s).runs){ ctx.lineWidth=r.w+bold; ctx.stroke(r.path); }
  ctx.restore();
}

// ─── Shape rendering ─────────────────────────────────────────────────────────
function renderShape(s) {
  if (!s) return;
  ctx.save();
  ctx.strokeStyle = s.strokeColor || '#ffffff';
  ctx.lineWidth   = Math.max(0.5, s.strokeWidth || 2);
  ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  ctx.setLineDash([]);

  switch (s.type) {
    case 'line':
      ctx.beginPath(); ctx.moveTo(s.v[0].x, s.v[0].y); ctx.lineTo(s.v[1].x, s.v[1].y); ctx.stroke();
      break;

    case 'dashedLine':
      ctx.setLineDash([10 / ctx.getTransform().a, 7 / ctx.getTransform().a]);
      ctx.beginPath(); ctx.moveTo(s.v[0].x, s.v[0].y); ctx.lineTo(s.v[1].x, s.v[1].y); ctx.stroke();
      ctx.setLineDash([]);
      break;

    case 'arrow': {
      const ang = Math.atan2(s.v[1].y - s.v[0].y, s.v[1].x - s.v[0].x);
      const hs  = Math.max(10, s.strokeWidth * 6);
      // Line ends at arrowhead base, not at tip
      const bx = s.v[1].x - Math.cos(ang) * hs;
      const by = s.v[1].y - Math.sin(ang) * hs;
      ctx.beginPath(); ctx.moveTo(s.v[0].x, s.v[0].y); ctx.lineTo(bx, by); ctx.stroke();
      // Filled arrowhead triangle
      ctx.beginPath();
      ctx.moveTo(s.v[1].x, s.v[1].y);
      ctx.lineTo(s.v[1].x - Math.cos(ang - 0.45) * hs, s.v[1].y - Math.sin(ang - 0.45) * hs);
      ctx.lineTo(s.v[1].x - Math.cos(ang + 0.45) * hs, s.v[1].y - Math.sin(ang + 0.45) * hs);
      ctx.closePath(); ctx.fillStyle = s.strokeColor; ctx.fill();
      break;
    }

    case 'rect':
    case 'square': {
      ctx.beginPath();
      ctx.moveTo(s.v[0].x, s.v[0].y);
      s.v.forEach((p, i) => { if (i > 0) ctx.lineTo(p.x, p.y); });
      ctx.closePath(); ctx.stroke();
      break;
    }

    case 'roundedRect': {
      const xs = s.v.map(p => p.x), ys = s.v.map(p => p.y);
      const x = Math.min(...xs), y = Math.min(...ys);
      const w = Math.max(...xs) - x, h = Math.max(...ys) - y;
      ctx.beginPath();
      ctx.roundRect(x, y, w, h, s.rx || Math.min(w, h) * 0.25);
      ctx.stroke();
      break;
    }

    case 'circle': {
      const r = Math.hypot(s.rp.x - s.cx, s.rp.y - s.cy);
      ctx.beginPath(); ctx.arc(s.cx, s.cy, Math.max(0.5, r), 0, Math.PI * 2); ctx.stroke();
      break;
    }

    case 'ellipse':
      ctx.beginPath();
      ctx.ellipse(s.cx, s.cy, Math.max(1, s.rx), Math.max(1, s.ry), 0, 0, Math.PI * 2);
      ctx.stroke();
      break;

    case 'goniometric': {
      const r = Math.hypot(s.rp.x - s.cx, s.rp.y - s.cy);
      if (r < 1) break;
      const { cx, cy } = s;
      const lw = Math.max(0.5, s.strokeWidth);
      const ah = lw * 5, aw = ah * 0.4;
      ctx.fillStyle = s.strokeColor || '#ffffff';

      // Circle
      ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.stroke();

      // X and Y axes — plain lines, no arrowheads
      ctx.beginPath();
      ctx.moveTo(cx - r, cy); ctx.lineTo(cx + r, cy);
      ctx.moveTo(cx, cy - r); ctx.lineTo(cx, cy + r);
      ctx.stroke();

      // Tick marks — inside only, short
      const tickLen = Math.min(lw * 4, r * 0.10);
      ctx.lineWidth = Math.max(0.3, lw * 0.5);
      GONIO_ANGLES.forEach(deg => {
        if (deg % 90 === 0) return;
        const rad = deg * Math.PI / 180;
        const cos = Math.cos(rad), sin = Math.sin(rad);
        ctx.beginPath();
        ctx.moveTo(cx + (r - tickLen) * cos, cy - (r - tickLen) * sin);
        ctx.lineTo(cx + r * cos,             cy - r * sin);
        ctx.stroke();
      });
      break;
    }

    case 'regularPolygon':
    case 'rightTriangle':
    case 'polygon': {
      if (s.v.length < 2) break;
      ctx.beginPath();
      ctx.moveTo(s.v[0].x, s.v[0].y);
      for (let i = 1; i < s.v.length; i++) ctx.lineTo(s.v[i].x, s.v[i].y);
      if (s.v.length >= 3 && s.closed !== false) ctx.closePath();
      ctx.stroke();
      break;
    }

    case 'cartesian':
    case 'cartesianQ1':
    case 'cartesianQ12': {
      const { ox, oy, xl, xr, yu, yd } = s;
      const lw = Math.max(0.5, s.strokeWidth);
      const ah = lw * 6, aw = ah * 0.45;
      ctx.fillStyle = s.strokeColor || '#ffffff';

      // X axis: line from left edge to arrowhead base, arrow only at right (+X)
      const xL = ox - xl, xR = ox + xr;
      ctx.beginPath();
      ctx.moveTo(xL, oy); ctx.lineTo(xR - ah, oy);
      ctx.stroke();
      ctx.beginPath(); ctx.moveTo(xR, oy);
      ctx.lineTo(xR - ah, oy - aw); ctx.lineTo(xR - ah, oy + aw);
      ctx.closePath(); ctx.fill();

      // Y axis: line from bottom edge to arrowhead base, arrow only at top (+Y)
      const yT = oy - yu, yB = oy + yd;
      ctx.beginPath();
      ctx.moveTo(ox, yB); ctx.lineTo(ox, yT + ah);
      ctx.stroke();
      ctx.beginPath(); ctx.moveTo(ox, yT);
      ctx.lineTo(ox - aw, yT + ah); ctx.lineTo(ox + aw, yT + ah);
      ctx.closePath(); ctx.fill();

      // Tick marks — short and subtle
      const tw = lw * 1.5;
      ctx.lineWidth = Math.max(0.3, lw * 0.5);
      const xTickMin = xl > 0 ? -xl + GRID_SIZE : GRID_SIZE;
      const xTickMax = xr - ah - GRID_SIZE * 0.3;
      for (let x = Math.ceil(xTickMin / GRID_SIZE) * GRID_SIZE; x <= xTickMax; x += GRID_SIZE) {
        ctx.beginPath(); ctx.moveTo(ox + x, oy - tw); ctx.lineTo(ox + x, oy + tw); ctx.stroke();
      }
      const yTickUp = yu - ah - GRID_SIZE * 0.3;
      for (let y = GRID_SIZE; y <= yTickUp; y += GRID_SIZE) {
        ctx.beginPath(); ctx.moveTo(ox - tw, oy - y); ctx.lineTo(ox + tw, oy - y); ctx.stroke();
      }
      for (let y = GRID_SIZE; y <= yd; y += GRID_SIZE) {
        ctx.beginPath(); ctx.moveTo(ox - tw, oy + y); ctx.lineTo(ox + tw, oy + y); ctx.stroke();
      }
      break;
    }

    case 'text': {
      ctx.save();
      ctx.font = `${s.fontSize}px system-ui,-apple-system,sans-serif`;
      ctx.fillStyle = s.strokeColor || '#ffffff';
      ctx.textBaseline = 'top';
      const lines = (s.content || '').split('\n');
      const lh = s.fontSize * 1.25;
      lines.forEach((line, i) => ctx.fillText(line, s.x, s.y + i * lh));
      ctx.restore();
      break;
    }
  }
  ctx.restore();
}

// Draw in-progress polygon: vertices so far + line to current cursor + close indicator
function renderPolyProgress() {
  const verts = ss.polyVerts;
  if (!verts.length || !ss.lastPointerScreen) return;
  const cur = toWorld(ss.lastPointerScreen.x, ss.lastPointerScreen.y);
  const snap = snapHG(cur);
  const t = tab().transform;
  ctx.save();
  // Live preview of in-progress polygon
  ctx.strokeStyle = state.activeColor;
  ctx.lineWidth = Math.max(0.5, shapeStrokeWidth());
  ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  ctx.setLineDash([8 / t.scale, 5 / t.scale]);
  ctx.beginPath();
  ctx.moveTo(verts[0].x, verts[0].y);
  verts.forEach((p, i) => { if (i > 0) ctx.lineTo(p.x, p.y); });
  ctx.lineTo(snap.x, snap.y);
  ctx.stroke();
  ctx.setLineDash([]);
  const POLY_CLOSE_R = 10; // screen-space radius in px
  // First-vertex indicator: filled circle → click to close as polygon
  ctx.fillStyle = state.activeColor;
  ctx.strokeStyle = '#fff';
  ctx.lineWidth = 1.5 / t.scale;
  ctx.beginPath();
  ctx.arc(verts[0].x, verts[0].y, POLY_CLOSE_R / t.scale, 0, Math.PI * 2);
  ctx.fill(); ctx.stroke();
  // Last-vertex indicator (only when ≥2 verts and different from first): stroke-only → click to end as polyline
  if (verts.length >= 2) {
    const lv = verts[verts.length - 1];
    ctx.setLineDash([3 / t.scale, 3 / t.scale]);
    ctx.strokeStyle = state.activeColor;
    ctx.lineWidth = 1.8 / t.scale;
    ctx.beginPath();
    ctx.arc(lv.x, lv.y, POLY_CLOSE_R / t.scale, 0, Math.PI * 2);
    ctx.stroke();
    ctx.setLineDash([]);
  }
  ctx.restore();
}

function buildShape(tool, start, end) {
  const base = { id: 's' + (++shapeIdSeq), type: tool, strokeColor: state.activeColor, strokeWidth: shapeStrokeWidth() };
  switch (tool) {
    case 'line':
    case 'dashedLine':
    case 'arrow':
      return { ...base, v: [start, end] };
    case 'regularPolygon': {
      // start and end define one base edge; polygon grows "above" the base
      const dx = end.x - start.x, dy = end.y - start.y;
      const L = Math.hypot(dx, dy);
      if (L < 1) return null;
      const n = ss.regularPolySides;
      const R = L / (2 * Math.sin(Math.PI / n));      // circumradius
      const apothem = R * Math.cos(Math.PI / n);      // center-to-base distance
      const mx = (start.x + end.x) / 2, my = (start.y + end.y) / 2;
      // Perpendicular unit vector pointing screen-upward (negative y)
      let perpX = -dy / L, perpY = dx / L;
      if (perpY > 0) { perpX = -perpX; perpY = -perpY; }
      const cx = mx + perpX * apothem, cy = my + perpY * apothem;
      // Vertices starting from 'start', going to 'end', then upward
      const angle0 = Math.atan2(start.y - cy, start.x - cx);
      const verts = [];
      for (let i = 0; i < n; i++) {
        const a = angle0 - (2 * Math.PI * i) / n;
        verts.push({ x: cx + R * Math.cos(a), y: cy + R * Math.sin(a) });
      }
      return { ...base, type: 'regularPolygon', v: verts };
    }
    case 'rightTriangle':
      // Right angle at bottom-left, base at bottom, height on left
      return { ...base, v:[{x:start.x,y:end.y},{x:end.x,y:end.y},{x:start.x,y:start.y}] };
    case 'rect':
      return { ...base, v: [start, {x:end.x,y:start.y}, end, {x:start.x,y:end.y}] };
    case 'square': {
      const dx = end.x - start.x, dy = end.y - start.y;
      const s = Math.sign(dx) * Math.max(Math.abs(dx), Math.abs(dy));
      const sy= Math.sign(dy) * Math.max(Math.abs(dx), Math.abs(dy));
      return { ...base, v: [start, {x:start.x+s,y:start.y}, {x:start.x+s,y:start.y+sy}, {x:start.x,y:start.y+sy}] };
    }
    case 'roundedRect': {
      const w = Math.abs(end.x - start.x), h = Math.abs(end.y - start.y);
      const rx = Math.min(w, h) * 0.25;
      return { ...base, v: [start, {x:end.x,y:start.y}, end, {x:start.x,y:end.y}], rx };
    }
    case 'circle':
      return { ...base, cx: start.x, cy: start.y, rp: end };
    case 'ellipse': {
      const cx = (start.x+end.x)/2, cy=(start.y+end.y)/2;
      return { ...base, cx, cy, rx: Math.abs(end.x-start.x)/2, ry: Math.abs(end.y-start.y)/2 };
    }
    case 'goniometric':
      return { ...base, cx: start.x, cy: start.y, rp: end };
    case 'cartesian': {
      // origin at start, symmetric axes in all 4 directions
      const xl = Math.abs(end.x - start.x), xr = xl;
      const yu = Math.abs(end.y - start.y), yd = yu;
      if (xl < 1 || yu < 1) return null;
      return { ...base, ox: start.x, oy: start.y, xl, xr, yu, yd };
    }
    case 'cartesianQ1': {
      // origin at start (bottom-left), positive X and Y only
      const xr = Math.abs(end.x - start.x);
      const yu = Math.abs(end.y - start.y);
      if (xr < 1 || yu < 1) return null;
      return { ...base, ox: start.x, oy: start.y, xl: 0, xr, yu, yd: 0 };
    }
    case 'cartesianQ12': {
      // origin at start (bottom-center), symmetric X, positive Y only
      const xl = Math.abs(end.x - start.x), xr = xl;
      const yu = Math.abs(end.y - start.y);
      if (xl < 1 || yu < 1) return null;
      return { ...base, ox: start.x, oy: start.y, xl, xr, yu, yd: 0 };
    }
    default: return null;
  }
}

// ─── Shape input handling ────────────────────────────────────────────────────
function startShape(e) {
  const tool = state.activeTool;
  const rawW = toWorld(e.clientX, e.clientY);
  const needsFullGridStart = tool === 'rightTriangle' || tool === 'cartesian' || tool === 'cartesianQ1' || tool === 'cartesianQ12' || tool === 'goniometric';
  let p = needsFullGridStart ? snapGrid(rawW) : snapHG(rawW);
  p = snapToGoniometric(e.clientX, e.clientY) || p;
  ss.lastPointerScreen = { x: e.clientX, y: e.clientY };

  if (tool === 'polygon') {
    const POLY_CLOSE_R = 10; // must match renderPolyProgress
    // Tap first vertex → close as polygon
    if (ss.polyVerts.length >= 3) {
      const fp = worldToScreen(ss.polyVerts[0].x, ss.polyVerts[0].y);
      if (Math.hypot(e.clientX - fp.x, e.clientY - fp.y) <= POLY_CLOSE_R) {
        finalizePolyShape(true); return;
      }
    }
    // Tap last vertex → end as open polyline (spezzata)
    if (ss.polyVerts.length >= 2) {
      const lv = ss.polyVerts[ss.polyVerts.length - 1];
      const lp = worldToScreen(lv.x, lv.y);
      if (Math.hypot(e.clientX - lp.x, e.clientY - lp.y) <= POLY_CLOSE_R) {
        finalizePolyShape(false); return;
      }
    }
    ss.polyVerts.push(p); ss.drawing = true; state.dirty = true; return;
  }

  // Drag shapes (includes triangle and rightTriangle now)
  ss.drawing = true; ss.startPt = p; ss.preview = null; state.dirty = true;
}

function updateShape(e) {
  if (!ss.drawing) return;
  ss.lastPointerScreen = { x: e.clientX, y: e.clientY };
  const tool = state.activeTool;

  if (tool === 'polygon') { state.dirty = true; return; }

  const needsGrid = tool === 'cartesian' || tool === 'cartesianQ1' || tool === 'cartesianQ12' || tool === 'rightTriangle';
  let end = needsGrid ? snapGrid(toWorld(e.clientX, e.clientY)) : snapHG(toWorld(e.clientX, e.clientY));
  end = snapToGoniometric(e.clientX, e.clientY) || end;
  if (state.straighten && (tool === 'line' || tool === 'dashedLine' || tool === 'arrow')) {
    end = straightenEnd(ss.startPt, end);
  }
  // regularPolygon: always straighten base to 0°/45°/90° increments for easy horizontal drawing
  if (tool === 'regularPolygon') end = straightenEnd(ss.startPt, end);
  ss.preview = buildShape(tool, ss.startPt, end);
  state.dirty = true;
}

function endShape(e) {
  if (!ss.drawing) return;
  const tool = state.activeTool;
  if (tool === 'polygon') return; // handled via click accumulation

  const needsGrid = tool === 'cartesian' || tool === 'cartesianQ1' || tool === 'cartesianQ12' || tool === 'rightTriangle';
  let end = needsGrid ? snapGrid(toWorld(e.clientX, e.clientY)) : snapHG(toWorld(e.clientX, e.clientY));
  end = snapToGoniometric(e.clientX, e.clientY) || end;
  if (state.straighten && (tool === 'line' || tool === 'dashedLine' || tool === 'arrow')) {
    end = straightenEnd(ss.startPt, end);
  }
  if (tool === 'regularPolygon') end = straightenEnd(ss.startPt, end);
  const shape = buildShape(tool, ss.startPt, end);
  if (shape) { pushUndo(); shape.seq = ++tab().seq; tab().shapes.push(shape); }
  ss.drawing = false; ss.preview = null; state.dirty = true;
}

function finalizePolyShape(closed = true) {
  if (ss.polyVerts.length < 2) { cancelPolyShape(); return; }
  const tool = state.activeTool;
  const shape = {
    id: 's' + (++shapeIdSeq), type: tool,
    v: [...ss.polyVerts],
    closed,  // false = open polyline (spezzata), true = closed polygon
    strokeColor: state.activeColor, strokeWidth: shapeStrokeWidth(),
  };
  pushUndo(); shape.seq = ++tab().seq; tab().shapes.push(shape);
  ss.drawing = false; ss.preview = null; ss.polyVerts = []; ss.triPhase = 0;
  state.dirty = true;
}

function cancelPolyShape() {
  ss.drawing = false; ss.preview = null; ss.polyVerts = []; ss.triPhase = 0; state.dirty = true;
}

// ─── Selection tool ───────────────────────────────────────────────────────────
function deepCloneShape(s) {
  const c = {...s};
  if (s.v) c.v = s.v.map(p => ({...p}));
  if (s.rp) c.rp = {...s.rp};
  return c;
}

function deepCloneItems(items) {
  return {
    strokes: items.strokes.map(s => ({...s, points: s.points.map(p=>({...p})), widths: s.widths?[...s.widths]:undefined})),
    highlighters: items.highlighters.map(s => ({...s, points: s.points.map(p=>({...p})), widths: s.widths?[...s.widths]:undefined})),
    shapes: items.shapes.map(s => deepCloneShape(s)),
  };
}

function pointInPoly(px, py, poly) {
  let inside = false;
  for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
    const xi=poly[i].x, yi=poly[i].y, xj=poly[j].x, yj=poly[j].y;
    if ((yi>py)!==(yj>py) && px < (xj-xi)*(py-yi)/(yj-yi)+xi) inside = !inside;
  }
  return inside;
}

function strokeBboxW(s) {
  let x0=Infinity,y0=Infinity,x1=-Infinity,y1=-Infinity;
  s.points.forEach(p=>{ if(p.x<x0)x0=p.x; if(p.x>x1)x1=p.x; if(p.y<y0)y0=p.y; if(p.y>y1)y1=p.y; });
  return {x:x0, y:y0, w:x1-x0, h:y1-y0};
}

function bboxIntersectsPoly(bbox, poly) {
  const corners = [{x:bbox.x,y:bbox.y},{x:bbox.x+bbox.w,y:bbox.y},{x:bbox.x,y:bbox.y+bbox.h},{x:bbox.x+bbox.w,y:bbox.y+bbox.h}];
  if (corners.some(c => pointInPoly(c.x,c.y,poly))) return true;
  if (poly.some(p => p.x>=bbox.x&&p.x<=bbox.x+bbox.w&&p.y>=bbox.y&&p.y<=bbox.y+bbox.h)) return true;
  return false;
}

function textBboxPoints(s) {
  const lines = (s.content || '').split('\n');
  const maxLen = Math.max(1, ...lines.map(l => l.length));
  const w = maxLen * s.fontSize * 0.58;
  const h = lines.length * s.fontSize * 1.25;
  return [{x:s.x, y:s.y}, {x:s.x+w, y:s.y+h}];
}

function shapeKeyPoints(s) {
  if (s.type==='text') return textBboxPoints(s);
  if (s.v) return s.v;
  if (s.type==='circle'||s.type==='goniometric') return [{x:s.cx,y:s.cy},s.rp];
  if (s.type==='ellipse') return [{x:s.cx,y:s.cy}];
  if (s.type==='cartesian'||s.type==='cartesianQ1'||s.type==='cartesianQ12') return [{x:s.ox,y:s.oy}];
  return [];
}
function shapeBboxPoints(s) {
  if (s.type==='text') return textBboxPoints(s);
  if (s.v) return s.v;
  if (s.type==='circle'||s.type==='goniometric') {
    const r=Math.hypot(s.rp.x-s.cx,s.rp.y-s.cy);
    return [{x:s.cx-r,y:s.cy-r},{x:s.cx+r,y:s.cy+r}];
  }
  if (s.type==='ellipse') return [{x:s.cx-s.rx,y:s.cy-s.ry},{x:s.cx+s.rx,y:s.cy+s.ry}];
  if (s.type==='cartesian') return [{x:s.ox-s.xl,y:s.oy-s.yu},{x:s.ox+s.xr,y:s.oy+s.yd}];
  if (s.type==='cartesianQ1') return [{x:s.ox,y:s.oy-s.yu},{x:s.ox+s.xr,y:s.oy}];
  if (s.type==='cartesianQ12') return [{x:s.ox-s.xl,y:s.oy-s.yu},{x:s.ox+s.xr,y:s.oy}];
  return shapeKeyPoints(s);
}

function computeSelection(lassoWorld) {
  const t = tab();
  return {
    strokes: t.strokes.filter(s => bboxIntersectsPoly(strokeBboxW(s), lassoWorld)),
    highlighters: t.highlighters.filter(s => bboxIntersectsPoly(strokeBboxW(s), lassoWorld)),
    shapes: t.shapes.filter(s => shapeKeyPoints(s).some(v => pointInPoly(v.x,v.y,lassoWorld))),
  };
}

function computeSelBbox(items) {
  let x0=Infinity,y0=Infinity,x1=-Infinity,y1=-Infinity;
  const ex=(x,y)=>{ if(x<x0)x0=x; if(x>x1)x1=x; if(y<y0)y0=y; if(y>y1)y1=y; };
  [...items.strokes,...items.highlighters].forEach(s=>s.points.forEach(p=>ex(p.x,p.y)));
  items.shapes.forEach(s=>shapeBboxPoints(s).forEach(v=>ex(v.x,v.y)));
  if (x0===Infinity) return null;
  const PAD = 10 / tab().transform.scale;
  return { x:x0-PAD, y:y0-PAD, w:x1-x0+PAD*2, h:y1-y0+PAD*2 };
}

function transformShapeCoords(shape, orig, fn) {
  if (orig.type==='text') { const r=fn(orig.x,orig.y); shape.x=r.x; shape.y=r.y; return; }
  if (orig.v) shape.v.forEach((p,i)=>{ const r=fn(orig.v[i].x,orig.v[i].y); p.x=r.x; p.y=r.y; });
  if (orig.rp!==undefined) { const r=fn(orig.rp.x,orig.rp.y); shape.rp={x:r.x,y:r.y}; }
  if (orig.cx!==undefined) { const r=fn(orig.cx,orig.cy); shape.cx=r.x; shape.cy=r.y; }
  if (orig.ox!==undefined) { const r=fn(orig.ox,orig.oy); shape.ox=r.x; shape.oy=r.y; }
}

function applyTranslate(items, origData, dx, dy) {
  const fn=(ox,oy)=>({x:ox+dx,y:oy+dy});
  items.strokes.forEach((s,si)=>s.points.forEach((p,pi)=>{ const o=origData.strokes[si].points[pi]; p.x=o.x+dx; p.y=o.y+dy; }));
  items.highlighters.forEach((s,si)=>s.points.forEach((p,pi)=>{ const o=origData.highlighters[si].points[pi]; p.x=o.x+dx; p.y=o.y+dy; }));
  items.shapes.forEach((shape,si)=>transformShapeCoords(shape,origData.shapes[si],fn));
  itemsChanged(items);
}

function applyResize(sx, sy) {
  const ob=sel.origBbox, wp=toWorld(sx,sy), h=sel.dragHandle;
  const L=ob.x, R=ob.x+ob.w, T=ob.y, B=ob.y+ob.h, CX=(L+R)/2, CY=(T+B)/2;
  const safe=(n,d)=>Math.abs(d)<0.001?1:n/d;
  const isCorner=['tl','tr','bl','br'].includes(h);

  let fx,fy,scaleX,scaleY;
  switch(h) {
    case 'tl': fx=R;fy=B; scaleX=safe(R-wp.x,ob.w); scaleY=safe(B-wp.y,ob.h); break;
    case 'tr': fx=L;fy=B; scaleX=safe(wp.x-L,ob.w); scaleY=safe(B-wp.y,ob.h); break;
    case 'bl': fx=R;fy=T; scaleX=safe(R-wp.x,ob.w); scaleY=safe(wp.y-T,ob.h); break;
    case 'br': fx=L;fy=T; scaleX=safe(wp.x-L,ob.w); scaleY=safe(wp.y-T,ob.h); break;
    case 'tm': fx=CX;fy=B; scaleX=1; scaleY=safe(B-wp.y,ob.h); break;
    case 'bm': fx=CX;fy=T; scaleX=1; scaleY=safe(wp.y-T,ob.h); break;
    case 'lm': fx=R;fy=CY; scaleX=safe(R-wp.x,ob.w); scaleY=1; break;
    case 'rm': fx=L;fy=CY; scaleX=safe(wp.x-L,ob.w); scaleY=1; break;
    default: return;
  }

  // Corner handles → proportional resize (project onto diagonal to get single scale factor)
  if (isCorner && ob.w>0.001 && ob.h>0.001) {
    const diagSq=ob.w*ob.w+ob.h*ob.h;
    const s=(scaleX*ob.w*ob.w+scaleY*ob.h*ob.h)/diagSq;
    scaleX=s; scaleY=s;
  }

  const fn=(ox,oy)=>({x:fx+(ox-fx)*scaleX, y:fy+(oy-fy)*scaleY});
  sel.items.strokes.forEach((s,si)=>s.points.forEach((p,pi)=>{ const r=fn(sel.origData.strokes[si].points[pi].x,sel.origData.strokes[si].points[pi].y); p.x=r.x; p.y=r.y; }));
  sel.items.highlighters.forEach((s,si)=>s.points.forEach((p,pi)=>{ const r=fn(sel.origData.highlighters[si].points[pi].x,sel.origData.highlighters[si].points[pi].y); p.x=r.x; p.y=r.y; }));
  sel.items.shapes.forEach((shape,si)=>{
    const orig=sel.origData.shapes[si];
    // Cartesian: origin stays fixed, midpoints extend one axis, corners extend two axes
    if (shape.type==='cartesian'||shape.type==='cartesianQ1'||shape.type==='cartesianQ12') {
      if (h==='tm'||h==='tl'||h==='tr') shape.yu=Math.max(GRID_SIZE, orig.oy-wp.y);
      if (h==='bm'||h==='bl'||h==='br') shape.yd=Math.max(GRID_SIZE, wp.y-orig.oy);
      if (h==='lm'||h==='tl'||h==='bl') shape.xl=Math.max(GRID_SIZE, orig.ox-wp.x);
      if (h==='rm'||h==='tr'||h==='br') shape.xr=Math.max(GRID_SIZE, wp.x-orig.ox);
      return;
    }
    transformShapeCoords(shape,orig,fn);
    if (shape.type==='ellipse') { shape.rx=orig.rx*Math.abs(scaleX); shape.ry=orig.ry*Math.abs(scaleY); }
  });
  itemsChanged(sel.items);
  sel.bbox = computeSelBbox(sel.items) || sel.bbox;
}

function applyRotation(sx, sy) {
  const ob=sel.origBbox, cx=ob.x+ob.w/2, cy=ob.y+ob.h/2;
  const cS=worldToScreen(cx,cy);
  const a0=Math.atan2(sel.dragStartScreen.y-cS.y, sel.dragStartScreen.x-cS.x);
  const a1=Math.atan2(sy-cS.y, sx-cS.x), rot=a1-a0;
  const cosR=Math.cos(rot), sinR=Math.sin(rot);
  const fn=(ox,oy)=>{ const dx=ox-cx,dy=oy-cy; return {x:cx+dx*cosR-dy*sinR, y:cy+dx*sinR+dy*cosR}; };
  sel.items.strokes.forEach((s,si)=>s.points.forEach((p,pi)=>{ const r=fn(sel.origData.strokes[si].points[pi].x,sel.origData.strokes[si].points[pi].y); p.x=r.x; p.y=r.y; }));
  sel.items.highlighters.forEach((s,si)=>s.points.forEach((p,pi)=>{ const r=fn(sel.origData.highlighters[si].points[pi].x,sel.origData.highlighters[si].points[pi].y); p.x=r.x; p.y=r.y; }));
  sel.items.shapes.forEach((shape,si)=>transformShapeCoords(shape,sel.origData.shapes[si],fn));
  itemsChanged(sel.items);
  sel.bbox = computeSelBbox(sel.items) || sel.bbox;
}

function getSelHandles() {
  if (!sel.bbox) return [];
  const b=sel.bbox, cx=b.x+b.w/2, cy=b.y+b.h/2;
  const hs=[
    {id:'tl',wx:b.x,    wy:b.y},
    {id:'tr',wx:b.x+b.w,wy:b.y},
    {id:'bl',wx:b.x,    wy:b.y+b.h},
    {id:'br',wx:b.x+b.w,wy:b.y+b.h},
    {id:'tm',wx:cx,     wy:b.y},
    {id:'bm',wx:cx,     wy:b.y+b.h},
    {id:'lm',wx:b.x,   wy:cy},
    {id:'rm',wx:b.x+b.w,wy:cy},
  ].map(h=>{ const s=worldToScreen(h.wx,h.wy); return {...h,sx:s.x,sy:s.y}; });
  const tmS=worldToScreen(cx,b.y);
  hs.push({id:'rotate',wx:cx,wy:b.y,sx:tmS.x,sy:tmS.y-36});
  return hs;
}

function hitTestHandle(sx, sy) {
  for (const h of getSelHandles()) { if (Math.hypot(sx-h.sx,sy-h.sy)<10) return h.id; }
  return null;
}

function hitTestBbox(sx, sy) {
  if (!sel.bbox) return false;
  const tl=worldToScreen(sel.bbox.x,sel.bbox.y), br=worldToScreen(sel.bbox.x+sel.bbox.w,sel.bbox.y+sel.bbox.h);
  return sx>=tl.x && sx<=br.x && sy>=tl.y && sy<=br.y;
}

// ─── Vertex editing helpers ───────────────────────────────────────────────────
function selSingleShape() {
  if (!sel.items) return null;
  if (sel.items.shapes.length!==1||sel.items.strokes.length||sel.items.highlighters.length) return null;
  return sel.items.shapes[0];
}

// Vertex handles only for shapes whose geometry is defined by free vertices
const VERTEX_EDIT_TYPES = new Set(['polygon','rightTriangle','line','dashedLine','arrow']);
function getVertexHandles(s) {
  if (!s.v || !VERTEX_EDIT_TYPES.has(s.type)) return [];
  return s.v.map((p,i)=>({id:'v'+i,wx:p.x,wy:p.y}));
}

function hitTestVertexHandle(sx,sy,shape) {
  for (const h of getVertexHandles(shape)) {
    const sp=worldToScreen(h.wx,h.wy);
    if (Math.hypot(sx-sp.x,sy-sp.y)<12) return h.id;
  }
  return null;
}

function applyVertexDrag(shape,hid,wx,wy) {
  const p=snapHG({x:wx,y:wy});
  if (hid.startsWith('v')) { const i=parseInt(hid.slice(1)); shape.v[i]={x:p.x,y:p.y}; }
  itemsChanged(null);
}

function clearSelection() {
  sel.phase='idle'; sel.items=null; sel.bbox=null; sel.lassoPoints=[];
  sel.origData=null; sel.origBbox=null; sel.dragHandle=null;
  sel.vertHandle=null; sel.vertOrigShape=null;
  const mb=document.getElementById('sel-minibar'); if(mb) mb.style.display='none';
  state.dirty=true;
}

function deleteSelection() {
  if (!sel.items) return;
  pushUndo();
  const t=tab();
  sel.items.strokes.forEach(s=>{ const i=t.strokes.indexOf(s); if(i!==-1)t.strokes.splice(i,1); });
  sel.items.highlighters.forEach(s=>{ const i=t.highlighters.indexOf(s); if(i!==-1)t.highlighters.splice(i,1); });
  sel.items.shapes.forEach(s=>{ const i=t.shapes.indexOf(s); if(i!==-1)t.shapes.splice(i,1); });
  clearSelection();
}

function copySelection() {
  if (!sel.items) return;
  sel.clipboard = deepCloneItems(sel.items);
  updatePasteBtn();
}

function scaleSelection(factor) {
  if (!sel.items||!sel.bbox) return;
  pushUndo(); detachSelection();
  const cx=sel.bbox.x+sel.bbox.w/2, cy=sel.bbox.y+sel.bbox.h/2;
  const scalePoint=(p)=>({x:cx+(p.x-cx)*factor, y:cy+(p.y-cy)*factor});
  const applyToShape=(s)=>{
    if (s.type==='text') { const p=scalePoint({x:s.x,y:s.y}); s.x=p.x; s.y=p.y; s.fontSize*=factor; return; }
    if (s.v) s.v=s.v.map(scalePoint);
    if (s.cx!==undefined) { const d=scalePoint({x:s.cx,y:s.cy}); s.cx=d.x; s.cy=d.y; }
    if (s.rp!==undefined) s.rp=scalePoint(s.rp);
    if (s.rx!==undefined) s.rx*=factor;
    if (s.ry!==undefined) s.ry*=factor;
    if (s.ox!==undefined) {
      const o=scalePoint({x:s.ox,y:s.oy}); s.ox=o.x; s.oy=o.y;
      s.xl*=factor; s.xr*=factor; s.yu*=factor; s.yd*=factor;
    }
    if (s.strokeWidth) s.strokeWidth*=factor;
  };
  const applyToStroke=(st)=>{
    st.points=st.points.map(p=>({...p,...scalePoint(p)}));
    if (st.widths) st.widths=st.widths.map(w=>w*factor);
    st.width*=factor;
  };
  sel.items.shapes.forEach(applyToShape);
  sel.items.strokes.forEach(applyToStroke);
  sel.items.highlighters.forEach(applyToStroke);
  itemsChanged(sel.items);
  sel.bbox = computeSelBbox(sel.items);
  state.dirty=true;
  positionSelMinibar();
}

// ─── Paste mode (click-to-place) ─────────────────────────────────────────────
let pasteMode = false;

function updatePasteBtn() {
  const fab = document.getElementById('paste-fab');
  if (fab) fab.style.display = sel.clipboard ? 'flex' : 'none';
}

function enterPasteMode() {
  if (!sel.clipboard) return;
  pasteMode = true;
  const fab = document.getElementById('paste-fab');
  fab.classList.add('paste-mode-active');
  document.getElementById('paste-fab-icon').innerHTML = '<line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/>';
  document.getElementById('paste-fab-label').textContent = 'Annulla';
  canvas.style.cursor = 'copy';
}

function exitPasteMode() {
  pasteMode = false;
  const fab = document.getElementById('paste-fab');
  fab.classList.remove('paste-mode-active');
  document.getElementById('paste-fab-icon').innerHTML = '<path d="M16 4h2a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2H6a2 2 0 0 1-2-2V6a2 2 0 0 1 2-2h2"/><rect x="8" y="2" width="8" height="4" rx="1"/>';
  document.getElementById('paste-fab-label').textContent = 'Incolla';
  canvas.style.cursor = 'crosshair';
}

function pasteAtPoint(wx, wy) {
  exitPasteMode(); // always revert button first
  if (!sel.clipboard) return;
  const clip = sel.clipboard;

  // Compute clipboard bounding box center
  let x0=Infinity, y0=Infinity, x1=-Infinity, y1=-Infinity;
  const ex=(x,y)=>{ if(x<x0)x0=x; if(x>x1)x1=x; if(y<y0)y0=y; if(y>y1)y1=y; };
  [...clip.strokes,...clip.highlighters].forEach(s=>s.points.forEach(p=>ex(p.x,p.y)));
  clip.shapes.forEach(s=>shapeKeyPoints(s).forEach(v=>ex(v.x,v.y)));
  const dx = x0===Infinity ? 0 : wx-(x0+x1)/2;
  const dy = y0===Infinity ? 0 : wy-(y0+y1)/2;

  pushUndo();
  const t = tab();
  const newItems = { strokes:[], highlighters:[], shapes:[] };

  clip.strokes.forEach(s=>{
    const c = {...s, points:s.points.map(p=>({x:p.x+dx,y:p.y+dy})), widths:s.widths?[...s.widths]:undefined, seq:++t.seq};
    t.strokes.push(c); newItems.strokes.push(c);
  });
  clip.highlighters.forEach(s=>{
    const c = {...s, points:s.points.map(p=>({x:p.x+dx,y:p.y+dy})), widths:s.widths?[...s.widths]:undefined, seq:++t.seq};
    t.highlighters.push(c); newItems.highlighters.push(c);
  });
  clip.shapes.forEach(s=>{
    const c = deepCloneShape(s); c.id='s'+(++shapeIdSeq); c.seq=++t.seq;
    if(c.v) c.v.forEach(p=>{p.x+=dx;p.y+=dy;});
    if(c.rp){c.rp.x+=dx;c.rp.y+=dy;}
    if(c.cx!==undefined){c.cx+=dx;c.cy+=dy;}
    if(c.ox!==undefined){c.ox+=dx;c.oy+=dy;}
    t.shapes.push(c); newItems.shapes.push(c);
  });

  // Switch to whichever selection tool is currently active, or default to select
  const pasteToolId = (state.activeTool==='touch') ? 'touch' : 'select';
  state.activeTool = pasteToolId;
  document.querySelectorAll('.tool-btn').forEach(b=>b.classList.remove('active-tool'));
  document.getElementById('btn-'+pasteToolId).classList.add('active-tool');
  document.getElementById('btn-shapes-toggle').classList.remove('active-tool');
  document.getElementById('rp-popup').style.display = 'none';
  sel.items = newItems;
  sel.bbox = computeSelBbox(newItems);
  sel.phase = 'selected';
  state.dirty = true;
}

function pasteSelection() {
  if (!sel.clipboard) return;
  pushUndo();
  const OFFSET=20, t=tab();
  const newItems={strokes:[],highlighters:[],shapes:[]};
  sel.clipboard.strokes.forEach(s=>{
    const c={...s,points:s.points.map(p=>({x:p.x+OFFSET,y:p.y+OFFSET})),widths:s.widths?[...s.widths]:undefined,seq:++t.seq};
    t.strokes.push(c); newItems.strokes.push(c);
  });
  sel.clipboard.highlighters.forEach(s=>{
    const c={...s,points:s.points.map(p=>({x:p.x+OFFSET,y:p.y+OFFSET})),widths:s.widths?[...s.widths]:undefined,seq:++t.seq};
    t.highlighters.push(c); newItems.highlighters.push(c);
  });
  sel.clipboard.shapes.forEach(s=>{
    const c=deepCloneShape(s); c.id='s'+(++shapeIdSeq); c.seq=++t.seq;
    if(c.v) c.v.forEach(p=>{p.x+=OFFSET;p.y+=OFFSET;});
    if(c.rp){c.rp.x+=OFFSET;c.rp.y+=OFFSET;}
    if(c.cx!==undefined){c.cx+=OFFSET;c.cy+=OFFSET;}
    if(c.ox!==undefined){c.ox+=OFFSET;c.oy+=OFFSET;}
    t.shapes.push(c); newItems.shapes.push(c);
  });
  sel.items=newItems; sel.bbox=computeSelBbox(newItems); sel.phase='selected';
  state.dirty=true;
}

function selStart(e) {
  const sx=e.clientX, sy=e.clientY;
  const activePhases = sel.phase==='selected'||sel.phase==='vertex'||sel.phase==='dragging'||sel.phase==='resizing'||sel.phase==='rotating';
  if (activePhases) {
    // Vertex handles have priority (only for single-shape selection)
    const single=selSingleShape();
    if (single&&(sel.phase==='selected'||sel.phase==='vertex')) {
      const vh=hitTestVertexHandle(sx,sy,single);
      if (vh) {
        pushUndo(); detachSelection();
        sel.phase='vertex'; sel.vertHandle=vh; sel.vertOrigShape=deepCloneShape(single);
        sel.dragStartWorld=toWorld(sx,sy); state.dirty=true; return;
      }
    }
    const handle=hitTestHandle(sx,sy);
    if (handle) {
      pushUndo(); detachSelection();
      sel.phase=handle==='rotate'?'rotating':'resizing';
      sel.dragHandle=handle; sel.dragStartScreen={x:sx,y:sy}; sel.dragStartWorld=toWorld(sx,sy);
      sel.origData=deepCloneItems(sel.items); sel.origBbox={...sel.bbox};
      state.dirty=true; return;
    }
    if (hitTestBbox(sx,sy)) {
      pushUndo(); detachSelection();
      sel.phase='dragging'; sel.dragHandle='move';
      sel.dragStartWorld=toWorld(sx,sy);
      sel.origData=deepCloneItems(sel.items); sel.origBbox={...sel.bbox};
      state.dirty=true; return;
    }
    clearSelection();
  }
  // Point hit test: click on item selects it immediately
  const hit=hitTestAnyItem(sx,sy);
  if (hit) {
    const items = hit.type==='shape'
      ? {strokes:[],highlighters:[],shapes:[hit.item]}
      : hit.type==='stroke'
        ? {strokes:[hit.item],highlighters:[],shapes:[]}
        : {strokes:[],highlighters:[hit.item],shapes:[]};
    sel.items=items; sel.bbox=computeSelBbox(items); sel.phase='selected';
    touchTapScreen={x:sx,y:sy};
    state.dirty=true; return;
  }
  sel.phase='lasso'; sel.lassoPoints=[{x:sx,y:sy}]; state.dirty=true;
}

function selMove(e) {
  const sx=e.clientX, sy=e.clientY;
  if (sel.phase==='lasso') { sel.lassoPoints.push({x:sx,y:sy}); state.dirty=true; return; }
  if (sel.phase==='vertex') {
    const wp=toWorld(sx,sy), single=selSingleShape();
    if (single) { applyVertexDrag(single,sel.vertHandle,wp.x,wp.y); sel.bbox=computeSelBbox(sel.items)||sel.bbox; }
    state.dirty=true; return;
  }
  if (sel.phase==='dragging') {
    const wp=toWorld(sx,sy), dx=wp.x-sel.dragStartWorld.x, dy=wp.y-sel.dragStartWorld.y;
    applyTranslate(sel.items,sel.origData,dx,dy);
    sel.bbox={x:sel.origBbox.x+dx,y:sel.origBbox.y+dy,w:sel.origBbox.w,h:sel.origBbox.h};
    lastDragScreen={x:sx,y:sy}; computeEdgeScroll(sx,sy);
    state.dirty=true; return;
  }
  if (sel.phase==='resizing') { applyResize(sx,sy); lastDragScreen={x:sx,y:sy}; computeEdgeScroll(sx,sy); state.dirty=true; return; }
  if (sel.phase==='rotating') { applyRotation(sx,sy); lastDragScreen={x:sx,y:sy}; computeEdgeScroll(sx,sy); state.dirty=true; return; }
  // Point-selected item: activate drag once threshold exceeded
  if (sel.phase==='selected'&&touchTapScreen) {
    const dist=Math.hypot(sx-touchTapScreen.x,sy-touchTapScreen.y);
    if (dist>6) {
      pushUndo(); detachSelection();
      sel.phase='dragging'; sel.dragHandle='move';
      sel.dragStartWorld=toWorld(touchTapScreen.x,touchTapScreen.y);
      sel.origData=deepCloneItems(sel.items); sel.origBbox={...sel.bbox};
      lastDragScreen={x:sx,y:sy};
      const wp=toWorld(sx,sy), dx=wp.x-sel.dragStartWorld.x, dy=wp.y-sel.dragStartWorld.y;
      applyTranslate(sel.items,sel.origData,dx,dy);
      sel.bbox={x:sel.origBbox.x+dx,y:sel.origBbox.y+dy,w:sel.origBbox.w,h:sel.origBbox.h};
      computeEdgeScroll(sx,sy); state.dirty=true;
    }
  }
}

function selUp(e) {
  if (sel.phase==='vertex') {
    sel.phase='selected'; sel.vertHandle=null; sel.vertOrigShape=null;
    const single=selSingleShape(); if(single) sel.bbox=computeSelBbox(sel.items)||sel.bbox;
    state.dirty=true;
  } else if (sel.phase==='lasso') {
    const lassoWorld=sel.lassoPoints.map(p=>toWorld(p.x,p.y));
    if (lassoWorld.length>=3) {
      const items=computeSelection(lassoWorld);
      if (items.strokes.length+items.highlighters.length+items.shapes.length>0) {
        sel.items=items; sel.bbox=computeSelBbox(items); sel.phase='selected';
      } else sel.phase='idle';
    } else sel.phase='idle';
    sel.lassoPoints=[]; state.dirty=true;
  } else if (sel.phase==='dragging'||sel.phase==='resizing'||sel.phase==='rotating') {
    sel.phase='selected'; sel.dragHandle=null; sel.origData=null; sel.origBbox=null;
    edgeScroll.vx=0; edgeScroll.vy=0; lastDragScreen=null;
    state.dirty=true;
  }
  touchTapScreen=null;
}

function positionSelMinibar() {
  const minibar=document.getElementById('sel-minibar');
  if (!sel.bbox||!sel.items) { minibar.style.display='none'; return; }
  if (sel.items.strokes.length+sel.items.highlighters.length+sel.items.shapes.length===0) { minibar.style.display='none'; return; }
  minibar.style.display='flex';
  const tl=worldToScreen(sel.bbox.x,sel.bbox.y), br=worldToScreen(sel.bbox.x+sel.bbox.w,sel.bbox.y+sel.bbox.h);
  const bCx=(tl.x+br.x)/2, miniW=minibar.offsetWidth||70;
  let top=br.y+10;
  if (top+50>window.innerHeight-8) top=tl.y-50;
  minibar.style.left=Math.max(8,Math.min(window.innerWidth-miniW-8,bCx-miniW/2))+'px';
  minibar.style.top=top+'px';
}

// ─── Edge scroll ─────────────────────────────────────────────────────────────
function computeEdgeScroll(sx, sy) {
  const W=canvas.width, H=canvas.height;
  let vx=0, vy=0;
  if (sx > W-EDGE_ZONE) vx = -((sx-(W-EDGE_ZONE))/EDGE_ZONE)*EDGE_MAX_SPEED;
  else if (sx < EDGE_ZONE) vx = ((EDGE_ZONE-sx)/EDGE_ZONE)*EDGE_MAX_SPEED;
  if (sy > H-EDGE_ZONE) vy = -((sy-(H-EDGE_ZONE))/EDGE_ZONE)*EDGE_MAX_SPEED;
  else if (sy < EDGE_ZONE) vy = ((EDGE_ZONE-sy)/EDGE_ZONE)*EDGE_MAX_SPEED;
  edgeScroll.vx=vx; edgeScroll.vy=vy;
}

function tickEdgeScroll() {
  if ((edgeScroll.vx===0&&edgeScroll.vy===0)||!lastDragScreen) return;
  const t=tab().transform;
  t.tx+=edgeScroll.vx; t.ty+=edgeScroll.vy;
  // Re-apply translate so items stay under pointer as canvas scrolls
  if (sel.phase==='dragging'&&sel.origData&&sel.origBbox&&sel.dragStartWorld) {
    const wp=toWorld(lastDragScreen.x,lastDragScreen.y);
    const dx=wp.x-sel.dragStartWorld.x, dy=wp.y-sel.dragStartWorld.y;
    applyTranslate(sel.items,sel.origData,dx,dy);
    sel.bbox={x:sel.origBbox.x+dx,y:sel.origBbox.y+dy,w:sel.origBbox.w,h:sel.origBbox.h};
  }
  state.dirty=true;
}

// ─── Touch-select hit testing ─────────────────────────────────────────────────
function distToSegSq(px,py,ax,ay,bx,by) {
  const dx=bx-ax, dy=by-ay, lenSq=dx*dx+dy*dy;
  if (lenSq===0) return (px-ax)**2+(py-ay)**2;
  const t=Math.max(0,Math.min(1,((px-ax)*dx+(py-ay)*dy)/lenSq));
  return (px-(ax+t*dx))**2+(py-(ay+t*dy))**2;
}

function hitTestStrokeByPoint(stroke, sx, sy) {
  const t=tab().transform;
  const hitR=Math.max(TAP_HIT_R, stroke.width*t.scale/2+4);
  const pts=stroke.points;
  for (let i=1;i<pts.length;i++) {
    const ax=pts[i-1].x*t.scale+t.tx, ay=pts[i-1].y*t.scale+t.ty;
    const bx=pts[i].x*t.scale+t.tx, by=pts[i].y*t.scale+t.ty;
    if (distToSegSq(sx,sy,ax,ay,bx,by)<hitR*hitR) return true;
  }
  return false;
}

function hitTestShape(s, sx, sy) {
  if (s.type==='text') {
    const pts=textBboxPoints(s);
    const tl=worldToScreen(pts[0].x,pts[0].y), br=worldToScreen(pts[1].x,pts[1].y);
    return sx>=tl.x&&sx<=br.x&&sy>=tl.y&&sy<=br.y;
  }
  const t=tab().transform;
  const M=Math.max(TAP_HIT_R,(s.strokeWidth||2)*t.scale/2+6);
  if (s.v && s.v.length>=2) {
    const sv=s.v.map(p=>worldToScreen(p.x,p.y));
    const isOpen=['line','dashedLine','arrow'].includes(s.type)||(s.closed===false);
    const segs=isOpen?sv.length-1:sv.length;
    for (let i=0;i<segs;i++) {
      const a=sv[i], b=sv[(i+1)%sv.length];
      if (distToSegSq(sx,sy,a.x,a.y,b.x,b.y)<M*M) return true;
    }
    if (!isOpen&&sv.length>=3) {
      const wp=toWorld(sx,sy);
      if (pointInPoly(wp.x,wp.y,s.v)) return true;
    }
    return false;
  }
  if (s.type==='circle'||s.type==='goniometric') {
    const c=worldToScreen(s.cx,s.cy);
    const rp=worldToScreen(s.rp.x,s.rp.y);
    const r=Math.hypot(rp.x-c.x,rp.y-c.y);
    const d=Math.hypot(sx-c.x,sy-c.y);
    return d<=r+M;
  }
  if (s.type==='ellipse') {
    const c=worldToScreen(s.cx,s.cy);
    const rx=s.rx*t.scale+M, ry=s.ry*t.scale+M;
    return ((sx-c.x)/rx)**2+((sy-c.y)/ry)**2<=1;
  }
  if (s.type==='cartesian'||s.type==='cartesianQ1'||s.type==='cartesianQ12') {
    const pts=shapeBboxPoints(s);
    let x0=Infinity,y0=Infinity,x1=-Infinity,y1=-Infinity;
    pts.forEach(p=>{ const sp=worldToScreen(p.x,p.y); x0=Math.min(x0,sp.x); x1=Math.max(x1,sp.x); y0=Math.min(y0,sp.y); y1=Math.max(y1,sp.y); });
    return sx>=x0-M&&sx<=x1+M&&sy>=y0-M&&sy<=y1+M;
  }
  return false;
}

function hitTestAnyItem(sx, sy) {
  const tb=tab();
  // Shapes (reverse order = top-first)
  for (let i=tb.shapes.length-1;i>=0;i--) {
    if (hitTestShape(tb.shapes[i],sx,sy)) return {type:'shape',item:tb.shapes[i]};
  }
  // Strokes (reverse order)
  for (let i=tb.strokes.length-1;i>=0;i--) {
    if (hitTestStrokeByPoint(tb.strokes[i],sx,sy)) return {type:'stroke',item:tb.strokes[i]};
  }
  for (let i=tb.highlighters.length-1;i>=0;i--) {
    if (hitTestStrokeByPoint(tb.highlighters[i],sx,sy)) return {type:'hl',item:tb.highlighters[i]};
  }
  return null;
}

// ─── Erasers ─────────────────────────────────────────────────────────────────
let pointEraserR = 20; // screen-space px, mutable via popup

let eraserActive = false;
let textEdit = { active: false, editingShape: null, wx: 0, wy: 0 };
let eraserUndoPushed = false;
let eraserPointerPos = null;
let lassoEraserPts = null;

// Split a freehand stroke into sub-strokes, removing the portion inside
// the eraser circle (world-space center wcx/wcy, radius wR).
function splitStroke(stroke, wcx, wcy, wR) {
  const pts = stroke.points, wids = stroke.widths;
  function inCircle(p) { return (p.x-wcx)**2+(p.y-wcy)**2 < wR*wR; }
  function lerpP(a,b,t) { return {x:a.x+(b.x-a.x)*t, y:a.y+(b.y-a.y)*t}; }
  function lerpW(i,j,t) { return wids ? wids[i]+(wids[j]-wids[i])*t : stroke.width; }
  // Returns t values where segment p1→p2 intersects the circle, sorted asc
  function circleTs(p1,p2) {
    const dx=p2.x-p1.x, dy=p2.y-p1.y;
    const fx=p1.x-wcx, fy=p1.y-wcy;
    const a=dx*dx+dy*dy; if(a<1e-12) return [];
    const b=2*(fx*dx+fy*dy), c=fx*fx+fy*fy-wR*wR;
    const disc=b*b-4*a*c; if(disc<0) return [];
    const sq=Math.sqrt(disc);
    return [(-b-sq)/(2*a),(-b+sq)/(2*a)].filter(t=>t>0&&t<1).sort((a,b)=>a-b);
  }

  const segments = [];
  let cur = null;

  for (let i=0; i<pts.length; i++) {
    const p = pts[i], inside = inCircle(p);
    if (!inside) {
      if (!cur) cur={points:[],widths:[]};
      cur.points.push(p);
      if (wids) cur.widths.push(wids[i]); else cur.widths.push(stroke.width);
      // Look ahead: if next point is inside, find entry intersection and close segment
      if (i+1<pts.length && inCircle(pts[i+1])) {
        const ts=circleTs(p,pts[i+1]);
        if (ts.length>0) {
          cur.points.push(lerpP(p,pts[i+1],ts[0]));
          cur.widths.push(lerpW(i,i+1,ts[0]));
        }
        if (cur.points.length>=2) segments.push(cur);
        cur=null;
      }
    } else {
      // Inside circle — look ahead: if next point is outside, find exit intersection
      if (i+1<pts.length && !inCircle(pts[i+1])) {
        const ts=circleTs(p,pts[i+1]);
        const exitT=ts.length>0?ts[ts.length-1]:0;
        cur={points:[lerpP(p,pts[i+1],exitT)],widths:[lerpW(i,i+1,exitT)]};
      }
    }
  }
  if (cur&&cur.points.length>=2) segments.push(cur);

  return segments.map(seg=>({
    ...stroke,
    points: seg.points,
    widths: seg.widths,
  }));
}

function hitTestStrokeEraser(stroke, sx, sy) {
  const t=tab().transform, R=pointEraserR;
  const pts=stroke.points;
  for (let i=1;i<pts.length;i++) {
    const ax=pts[i-1].x*t.scale+t.tx, ay=pts[i-1].y*t.scale+t.ty;
    const bx=pts[i].x*t.scale+t.tx,   by=pts[i].y*t.scale+t.ty;
    if (distToSegSq(sx,sy,ax,ay,bx,by)<R*R) return true;
  }
  if (pts.length===1) {
    const px=pts[0].x*t.scale+t.tx, py=pts[0].y*t.scale+t.ty;
    if ((sx-px)**2+(sy-py)**2<R*R) return true;
  }
  return false;
}

function pointEraserApply(sx, sy) {
  const tb=tab(), t=tb.transform;
  const wcx=(sx-t.tx)/t.scale, wcy=(sy-t.ty)/t.scale, wR=pointEraserR/t.scale;
  let changed=false;

  const splitList = arr => {
    const out=[];
    for (const s of arr) {
      if (!hitTestStrokeEraser(s,sx,sy)) { out.push(s); continue; }
      const segs=splitStroke(s,wcx,wcy,wR);
      out.push(...segs);
      changed=true;
    }
    return out;
  };

  const newStrokes=splitList(tb.strokes);
  const newHL=splitList(tb.highlighters);
  // Shapes: whole-object deletion (splitting a polygon geometrically is ill-defined)
  const newShapes=tb.shapes.filter(s=>{
    if(hitTestShape(s,sx,sy)){changed=true;return false;}return true;
  });

  if (changed) {
    if (!eraserUndoPushed) { pushUndo(); eraserUndoPushed=true; }
    tb.strokes=newStrokes; tb.highlighters=newHL; tb.shapes=newShapes;
    state.dirty=true;
  }
}

function pointEraserStart(e) {
  eraserActive=true; eraserUndoPushed=false;
  eraserPointerPos={x:e.clientX,y:e.clientY};
  pointEraserApply(e.clientX,e.clientY);
}
function pointEraserMove(e) {
  eraserPointerPos={x:e.clientX,y:e.clientY};
  if (eraserActive) pointEraserApply(e.clientX,e.clientY);
  state.dirty=true;
}
function pointEraserUp() { eraserActive=false; }

// Lasso eraser — identical selection logic to lasso-select, then delete
function lassoEraserStart(e) { lassoEraserPts=[{x:e.clientX,y:e.clientY}]; state.dirty=true; }
function lassoEraserMove(e) {
  if (!lassoEraserPts) return;
  lassoEraserPts.push({x:e.clientX,y:e.clientY});
  state.dirty=true;
}
function lassoEraserUp() {
  if (!lassoEraserPts||lassoEraserPts.length<3) { lassoEraserPts=null; state.dirty=true; return; }
  const lassoWorld=lassoEraserPts.map(p=>toWorld(p.x,p.y));
  lassoEraserPts=null; state.dirty=true;
  const selected=computeSelection(lassoWorld);
  if (!selected.strokes.length&&!selected.highlighters.length&&!selected.shapes.length) return;
  pushUndo();
  const tb=tab();
  const rmS=new Set(selected.strokes), rmH=new Set(selected.highlighters), rmSh=new Set(selected.shapes);
  tb.strokes=tb.strokes.filter(s=>!rmS.has(s));
  tb.highlighters=tb.highlighters.filter(s=>!rmH.has(s));
  tb.shapes=tb.shapes.filter(s=>!rmSh.has(s));
  state.dirty=true;
}

// ─── Pan tool (touch) ─────────────────────────────────────────────────────────
function touchSelStart(e) {
  const sx=e.clientX, sy=e.clientY;
  touchPan=true;
  const t=tab().transform;
  touchPanTx0=t.tx; touchPanTy0=t.ty;
  touchPanScreen0={x:sx,y:sy};
  canvas.style.cursor='grabbing';
}

function touchSelMove(e) {
  const sx=e.clientX, sy=e.clientY;
  if (touchPan&&touchPanScreen0) {
    const t=tab().transform;
    t.tx=touchPanTx0+(sx-touchPanScreen0.x);
    t.ty=touchPanTy0+(sy-touchPanScreen0.y);
    state.dirty=true;
  }
}

function touchSelUp(e) {
  touchPan=false; touchPanScreen0=null;
  canvas.style.cursor='grab';
  state.dirty=true;
}

function renderSelOverlay() {
  const selActive = state.activeTool==='select'||state.activeTool==='touch';
  if (!selActive) { document.getElementById('sel-minibar').style.display='none'; return; }
  ctx.save();
  ctx.setTransform(1,0,0,1,0,0);
  if (sel.phase==='lasso'&&sel.lassoPoints.length>1) {
    ctx.beginPath();
    ctx.moveTo(sel.lassoPoints[0].x,sel.lassoPoints[0].y);
    sel.lassoPoints.forEach((p,i)=>{ if(i>0) ctx.lineTo(p.x,p.y); });
    ctx.setLineDash([6,4]); ctx.strokeStyle='rgba(100,180,255,0.8)';
    ctx.lineWidth=1.5; ctx.lineCap='round'; ctx.stroke(); ctx.setLineDash([]);
  }
  const activePhase=sel.phase==='selected'||sel.phase==='vertex';
  if (activePhase&&sel.bbox) {
    const tl=worldToScreen(sel.bbox.x,sel.bbox.y), br=worldToScreen(sel.bbox.x+sel.bbox.w,sel.bbox.y+sel.bbox.h);
    ctx.setLineDash([6,4]); ctx.strokeStyle='rgba(100,180,255,0.8)';
    ctx.lineWidth=1.5; ctx.strokeRect(tl.x,tl.y,br.x-tl.x,br.y-tl.y); ctx.setLineDash([]);
    getSelHandles().forEach(h=>{
      ctx.beginPath(); ctx.arc(h.sx,h.sy,h.id==='rotate'?5:6,0,Math.PI*2);
      ctx.fillStyle='#fff'; ctx.fill();
      ctx.strokeStyle='rgba(100,180,255,0.9)'; ctx.lineWidth=1.5; ctx.stroke();
    });
    // Vertex handles — shown when a single shape is selected
    const single=selSingleShape();
    if (single&&(sel.phase==='selected'||sel.phase==='vertex')) {
      getVertexHandles(single).forEach(h=>{
        const sp=worldToScreen(h.wx,h.wy);
        ctx.beginPath(); ctx.arc(sp.x,sp.y,7,0,Math.PI*2);
        ctx.fillStyle='#fff'; ctx.fill();
        ctx.strokeStyle=single.strokeColor||state.activeColor; ctx.lineWidth=2; ctx.stroke();
      });
    }
    positionSelMinibar();
  } else if (sel.phase!=='lasso') {
    document.getElementById('sel-minibar').style.display='none';
  }
  ctx.restore();
}

function drawLaser() {
  if(!state.laser||!state.laser.points.length) return;
  const elapsed=Date.now()-state.laser.lastTime;
  if(elapsed>=LASER_TTL){state.laser=null;return;}
  const t=tab().transform;
  ctx.save();
  ctx.setTransform(t.scale,0,0,t.scale,t.tx,t.ty);
  ctx.globalAlpha=1-elapsed/LASER_TTL;
  ctx.beginPath(); catmull(state.laser.points,0.4);
  ctx.strokeStyle='#FF3333'; ctx.lineWidth=Math.max(0.5,getRawWidth('laser'));
  ctx.lineCap='round'; ctx.lineJoin='round'; ctx.stroke();
  ctx.restore();
  state.dirty=true;
}

// Baked layer — background, grid and every finished item, painted offscreen and
// reused until the view or the content changes. While a stroke is being drawn each
// frame just copies this layer and adds the live stroke (always the newest seq, so
// it belongs on top anyway).
const baked=document.createElement('canvas');
let bakedKey='', bakedRefs=[];
function liveCount(arr){ return arr.length-(curStroke&&arr[arr.length-1]===curStroke?1:0); }
function bakeScene(t) {
  const realCtx=ctx; ctx=baked.getContext('2d');
  ctx.save();
  ctx.setTransform(1,0,0,1,0,0);
  ctx.fillStyle=t.bgColor; ctx.fillRect(0,0,baked.width,baked.height);
  const {scale,tx,ty}=t.transform;
  ctx.setTransform(scale,0,0,scale,tx,ty);
  if(t.gridEnabled) drawGrid(t);
  // Only what intersects the screen gets drawn
  const vx0=-tx/scale, vy0=-ty/scale, vx1=(baked.width-tx)/scale, vy1=(baked.height-ty)/scale;
  const _all=[...t.highlighters,...t.strokes,...t.shapes].sort((a,b)=>(a.seq||0)-(b.seq||0));
  for(const s of _all){
    if(s===curStroke) continue;
    if(s.type){ renderShape(s); continue; }
    if(s.points.length>1){
      const b=strokeGeom(s).bbox;
      if(b.x1<vx0||b.x0>vx1||b.y1<vy0||b.y0>vy1) continue;
    }
    drawStroke(s);
  }
  ctx.restore();
  ctx=realCtx;
}

function render() {
  if(!state.dirty) return;
  state.dirty=false;
  const t=tab();
  if(baked.width!==canvas.width||baked.height!==canvas.height){ baked.width=canvas.width; baked.height=canvas.height; bakedKey=''; }
  const tr=t.transform;
  const key=[canvas.width,canvas.height,tr.scale,tr.tx,tr.ty,t.bgColor,t.gridEnabled,
             liveCount(t.strokes),liveCount(t.highlighters),t.shapes.length,sceneVer].join('|');
  const refs=[t,t.strokes,t.highlighters,t.shapes];
  if(key!==bakedKey||refs.some((r,i)=>r!==bakedRefs[i])){ bakeScene(t); bakedKey=key; bakedRefs=refs; }
  ctx.save();
  ctx.setTransform(1,0,0,1,0,0);
  ctx.drawImage(baked,0,0);
  ctx.setTransform(tr.scale,0,0,tr.scale,tr.tx,tr.ty);
  if(curStroke&&curStroke.tool!=='laser'){
    const arr=curStroke.tool==='highlighter'?t.highlighters:t.strokes;
    if(arr[arr.length-1]===curStroke) drawStroke(curStroke);
  }
  if (ss.preview) renderShape(ss.preview);
  if (ss.drawing && state.activeTool==='polygon') renderPolyProgress();
  ctx.restore();
  drawLaser();
  renderSelOverlay();
  renderEraserOverlay();
}
function renderEraserOverlay() {
  ctx.save(); ctx.setTransform(1,0,0,1,0,0);
  // Point eraser: dashed circle at pointer, color contrasted against bg
  if (state.activeTool==='pointEraser'&&eraserPointerPos) {
    const bg=tab().bgColor;
    const r=parseInt(bg.slice(1,3),16)/255, g=parseInt(bg.slice(3,5),16)/255, b=parseInt(bg.slice(5,7),16)/255;
    const lum=0.2126*r+0.7152*g+0.0722*b;
    const col=lum>0.4?'rgba(40,40,40,0.8)':'rgba(210,210,210,0.8)';
    ctx.beginPath(); ctx.arc(eraserPointerPos.x,eraserPointerPos.y,pointEraserR,0,Math.PI*2);
    ctx.setLineDash([4,3]); ctx.strokeStyle=col; ctx.lineWidth=1.5; ctx.stroke(); ctx.setLineDash([]);
  }
  // Lasso eraser: red dashed outline
  if (state.activeTool==='lassoEraser'&&lassoEraserPts&&lassoEraserPts.length>1) {
    ctx.beginPath();
    ctx.moveTo(lassoEraserPts[0].x,lassoEraserPts[0].y);
    lassoEraserPts.forEach((p,i)=>{ if(i>0) ctx.lineTo(p.x,p.y); });
    ctx.setLineDash([6,4]); ctx.strokeStyle='rgba(255,60,60,0.85)';
    ctx.lineWidth=1.5; ctx.lineCap='round'; ctx.stroke(); ctx.setLineDash([]);
  }
  ctx.restore();
}
function loop(){tickEdgeScroll();render();requestAnimationFrame(loop);}
requestAnimationFrame(loop);

// ─── Pointer / draw input ────────────────────────────────────────────────────
const ptrs = new Map();
let curStroke=null, drawing=false, panning=false, lastDist=null, lastMid=null;

canvas.addEventListener('pointerdown', onDown);
canvas.addEventListener('pointermove', onMove);
canvas.addEventListener('pointerup',   onUp);
canvas.addEventListener('pointercancel', onUp);
// Track pointer position for eraser circle even when not drawing
canvas.addEventListener('pointermove', e=>{
  if(state.activeTool==='pointEraser'){eraserPointerPos={x:e.clientX,y:e.clientY};state.dirty=true;}
  else if(state.activeTool!=='pointEraser'&&eraserPointerPos){eraserPointerPos=null;state.dirty=true;}
},{passive:true});
canvas.addEventListener('pointerleave', ()=>{ if(eraserPointerPos){eraserPointerPos=null;state.dirty=true;} },{passive:true});

function onDown(e) {
  e.preventDefault();
  // Confirm active text edit when tapping canvas (but not if text tool — that opens a new edit)
  if (textEdit.active && state.activeTool !== 'text') confirmText();
  canvas.setPointerCapture(e.pointerId);
  ptrs.set(e.pointerId,{x:e.clientX,y:e.clientY,pressure:e.pressure,type:e.pointerType});
  if (pasteMode && ptrs.size===1) {
    const wp = toWorld(e.clientX, e.clientY);
    pasteAtPoint(wp.x, wp.y);
    return;
  }
  if(ptrs.size===2){
    if(drawing) cancelStroke();
    if(ss.drawing) cancelPolyShape();
    touchPan=false; // cancel single-finger pan if second finger lands
    panning=true;
    const a=[...ptrs.values()];
    lastDist=Math.hypot(a[0].x-a[1].x,a[0].y-a[1].y);
    lastMid={x:(a[0].x+a[1].x)/2,y:(a[0].y+a[1].y)/2};
    return;
  }
  panning=false;
  if (SHAPE_TOOLS.has(state.activeTool)) startShape(e);
  else if (state.activeTool==='select') selStart(e);
  else if (state.activeTool==='touch') touchSelStart(e);
  else if (state.activeTool==='pointEraser') pointEraserStart(e);
  else if (state.activeTool==='lassoEraser') lassoEraserStart(e);
  else if (state.activeTool==='text') textToolDown(e);
  else startStroke(e);
}
function onMove(e) {
  e.preventDefault();
  if(!ptrs.has(e.pointerId)) return;
  ptrs.set(e.pointerId,{x:e.clientX,y:e.clientY,pressure:e.pressure,type:e.pointerType});
  if(panning||ptrs.size===2){
    const a=[...ptrs.values()];
    const dist=Math.hypot(a[0].x-a[1].x,a[0].y-a[1].y);
    const mid={x:(a[0].x+a[1].x)/2,y:(a[0].y+a[1].y)/2};
    const t=tab().transform;
    if(lastDist){const zf=dist/lastDist,ns=Math.min(Math.max(t.scale*zf,0.05),50);t.tx=mid.x-(mid.x-t.tx)*(ns/t.scale);t.ty=mid.y-(mid.y-t.ty)*(ns/t.scale);t.scale=ns;updateZoomLabel();}
    if(lastMid){t.tx+=mid.x-lastMid.x;t.ty+=mid.y-lastMid.y;}
    lastDist=dist;lastMid=mid;state.dirty=true;return;
  }
  if (SHAPE_TOOLS.has(state.activeTool)) { if(ss.drawing||state.activeTool==='polygon') updateShape(e); }
  else if (state.activeTool==='select') { if(sel.phase!=='idle') selMove(e); }
  else if (state.activeTool==='touch') touchSelMove(e);
  else if (state.activeTool==='pointEraser') pointEraserMove(e);
  else if (state.activeTool==='lassoEraser') lassoEraserMove(e);
  else if(drawing&&curStroke) extendStroke(e);
}
function onUp(e) {
  e.preventDefault();
  ptrs.delete(e.pointerId);
  if(ptrs.size<2){lastDist=null;lastMid=null;panning=false;}
  if (SHAPE_TOOLS.has(state.activeTool)) {
    if (ss.drawing && ptrs.size===0 && state.activeTool!=='polygon') endShape(e);
  } else if (state.activeTool==='select') {
    if (ptrs.size===0) selUp(e);
  } else if (state.activeTool==='touch') {
    if (ptrs.size===0) touchSelUp(e);
  } else if (state.activeTool==='pointEraser') {
    if (ptrs.size===0) pointEraserUp();
  } else if (state.activeTool==='lassoEraser') {
    if (ptrs.size===0) lassoEraserUp();
  } else if(drawing&&ptrs.size===0) endStroke();
}

function startStroke(e) {
  const tool=state.activeTool;
  if(tool!=='laser') pushUndo(); // snapshot BEFORE stroke is added
  const wp=toWorld(e.clientX,e.clientY);
  const bw=getRawWidth(tool);
  curStroke={
    points:[wp],widths:[bw],
    color:tool==='laser'?'#FF3333':tool==='highlighter'?state.highlighterColor:state.activeColor,
    width:bw, tension:e.pointerType==='pen'?0.4:0.6,
    tool, alpha:tool==='highlighter'?0.4:null,
    seq: tool!=='laser' ? ++tab().seq : 0,
  };
  if(tool==='laser') state.laser={points:[wp],lastTime:Date.now()};
  drawing=true; state.dirty=true;
}
function extendStroke(e) {
  // When a frame runs long the browser merges the pen samples it received into a
  // single pointermove; replay all of them, or the curve turns into a polyline.
  const evs=e.getCoalescedEvents?e.getCoalescedEvents():[];
  if(evs.length) evs.forEach(addStrokePoint); else addStrokePoint(e);
}
function addStrokePoint(e) {
  const wp=toWorld(e.clientX,e.clientY), tool=state.activeTool;
  if(tool==='laser'){
    if(state.laser){state.laser.points.push(wp);state.laser.lastTime=Date.now();}
    state.dirty=true; return;
  }
  // Skip point if too close to last — avoids micro-jitter creating jagged corners
  if(curStroke.points.length>0){
    const last=curStroke.points[curStroke.points.length-1];
    const minD=1.5/tab().transform.scale;
    if(Math.hypot(wp.x-last.x,wp.y-last.y)<minD) return;
  }
  const bw=getRawWidth(tool);
  let w=bw;
  if(e.pointerType==='pen'&&tool!=='highlighter') w=bw*(0.7+(e.pressure>0?e.pressure:0.5)*0.6);
  curStroke.points.push(wp); curStroke.widths.push(w);
  const arr=tool==='highlighter'?tab().highlighters:tab().strokes;
  if(!arr.length||arr[arr.length-1]!==curStroke) arr.push(curStroke);
  state.dirty=true;
}
function endStroke() {
  drawing=false; if(!curStroke) return;
  const tool=curStroke.tool;
  if(tool==='laser'){if(state.laser)state.laser.lastTime=Date.now();curStroke=null;return;}
  const arr=tool==='highlighter'?tab().highlighters:tab().strokes;
  if(!arr.length||arr[arr.length-1]!==curStroke) arr.push(curStroke);
  curStroke=null; state.dirty=true;
}
function cancelStroke() {
  if(!curStroke) return;
  if(curStroke.tool!=='laser') { tab().undoStack.pop(); syncUndoUI(); } // revert speculative push
  const arr=curStroke.tool==='highlighter'?tab().highlighters:tab().strokes;
  const i=arr.indexOf(curStroke); if(i!==-1) arr.splice(i,1);
  curStroke=null; drawing=false; state.dirty=true;
}

// ─── Undo / redo ─────────────────────────────────────────────────────────────
// Snapshots copy the arrays, not the items: copying every stroke on every action
// made memory grow with the square of the strokes on the board. Sharing is safe
// because an item is never edited in place after a snapshot — edits go through
// detachSelection() / confirmText(), which swap in a private copy first.
function snap(){const t=tab();return{strokes:[...t.strokes],highlighters:[...t.highlighters],shapes:[...t.shapes]};}
function detachSelection(){
  if(!sel.items) return;
  const t=tab();
  const swap=(arr,list,clone)=>list.map(o=>{ const c=clone(o), i=arr.indexOf(o); if(i!==-1) arr[i]=c; return c; });
  const cloneStroke=s=>({...s,points:s.points.map(p=>({...p})),widths:s.widths?[...s.widths]:undefined});
  sel.items={
    strokes:swap(t.strokes,sel.items.strokes,cloneStroke),
    highlighters:swap(t.highlighters,sel.items.highlighters,cloneStroke),
    shapes:swap(t.shapes,sel.items.shapes,deepCloneShape),
  };
}
function pushUndo(){tab().undoStack.push(snap());tab().redoStack=[];syncUndoUI();}
function undo(){const t=tab();if(!t.undoStack.length)return;t.redoStack.push(snap());const s=t.undoStack.pop();t.strokes=s.strokes;t.highlighters=s.highlighters;t.shapes=s.shapes||[];state.dirty=true;syncUndoUI();}
function redo(){const t=tab();if(!t.redoStack.length)return;t.undoStack.push(snap());const s=t.redoStack.pop();t.strokes=s.strokes;t.highlighters=s.highlighters;t.shapes=s.shapes||[];state.dirty=true;syncUndoUI();}
function syncUndoUI(){
  const canUndo=tab().undoStack.length?'1':'0.35';
  const canRedo=tab().redoStack.length?'1':'0.35';
  document.getElementById('btn-undo').style.opacity=canUndo;
  document.getElementById('btn-redo').style.opacity=canRedo;
  document.getElementById('btn-undo2').style.opacity=canUndo;
  document.getElementById('btn-redo2').style.opacity=canRedo;
}
document.addEventListener('keydown',e=>{
  if(e.ctrlKey||e.metaKey){
    if(e.key==='z'&&!e.shiftKey){e.preventDefault();undo();}
    if((e.key==='z'&&e.shiftKey)||e.key==='y'){e.preventDefault();redo();}
    if(e.key==='c'&&(state.activeTool==='select'||state.activeTool==='touch')){e.preventDefault();copySelection();}
    if(e.key==='v'&&sel.clipboard){e.preventDefault();pasteSelection();} // Ctrl+V: paste at +20px offset (keyboard fallback)
  }
  if((e.key==='Delete'||e.key==='Backspace')&&(state.activeTool==='select'||state.activeTool==='touch')){e.preventDefault();deleteSelection();}
  if(e.key==='Escape'&&pasteMode){e.preventDefault();exitPasteMode();}
});

// ─── Panel drag & snap ───────────────────────────────────────────────────────
const toolbar      = document.getElementById('toolbar');
const palettePanel = document.getElementById('palette-panel');
const tabPanel     = document.getElementById('tab-panel');
const historyPanel = document.getElementById('history-panel');
const canvasPanel  = document.getElementById('canvas-panel');
const ALL_PANELS   = [toolbar, palettePanel, tabPanel, historyPanel, canvasPanel];

// Each edge has 3 snap zones: start / center / end
// Vertical edges  (left/right): start=top,    center=middle, end=bottom
// Horizontal edges (top/bottom): start=left,  center=middle, end=right
// Panels in the same zone are layered outward from the edge (never side-by-side).

function applyZone(el, edge, zone) {
  el.dataset.edge = edge;
  el.dataset.zone = zone;
  el.classList.remove('edge-left','edge-right','edge-top','edge-bottom');
  el.classList.add('edge-'+edge);
  // Clear all inline position + layout overrides; repositionPanels sets them
  el.style.left=''; el.style.right=''; el.style.top=''; el.style.bottom='';
  el.style.transform='none'; el.style.flexDirection='';
}

function snapToZone(el) {
  const r  = el.getBoundingClientRect();
  const cx = r.left+r.width/2, cy = r.top+r.height/2;
  const W  = window.innerWidth, H = window.innerHeight;
  const d  = {left:cx, right:W-cx, top:cy, bottom:H-cy};
  const edge = Object.keys(d).reduce((a,b)=>d[a]<d[b]?a:b);
  const isVert = edge==='left'||edge==='right';
  const pos = isVert ? cy/H : cx/W;
  const zone = pos < 1/3 ? 'start' : pos > 2/3 ? 'end' : 'center';
  applyZone(el, edge, zone);
  repositionPanels();
}

// Position every snapped panel: zone controls the along-edge axis,
// layering controls how far from the edge each panel sits.
function repositionPanels() {
  const GAP = 8, MARGIN = 12;
  requestAnimationFrame(()=>{
    // Group by edge+zone key
    const groups = {};
    ALL_PANELS.forEach(p => {
      const edge = p.dataset.edge, zone = p.dataset.zone || 'center';
      if (!edge || edge==='float') return;
      const key = edge+':'+zone;
      if (!groups[key]) groups[key] = {edge, zone, panels:[]};
      groups[key].panels.push(p);
    });

    Object.values(groups).forEach(({edge, zone, panels}) => {
      const isVert = edge==='left'||edge==='right';

      // Apply zone positioning on the along-edge axis.
      // All four position properties start cleared so the browser uses 'auto',
      // which for position:fixed means the edge we DO set drives placement.
      panels.forEach(p => {
        p.style.left=''; p.style.right=''; p.style.top=''; p.style.bottom='';
        if (isVert) {
          // Y axis (along vertical edge)
          if (zone==='start')    { p.style.top    = MARGIN+'px'; p.style.transform='none'; }
          else if (zone==='end') { p.style.bottom = MARGIN+'px'; p.style.transform='none'; }
          else                   { p.style.top='50%'; p.style.transform='translateY(-50%)'; }
        } else {
          // X axis (along horizontal edge)
          if (zone==='start')    { p.style.left  = MARGIN+'px'; p.style.transform='none'; }
          else if (zone==='end') { p.style.right = MARGIN+'px'; p.style.transform='none'; }
          else                   { p.style.left='50%'; p.style.transform='translateX(-50%)'; }
        }
      });

      // Layer panels outward from the edge (perpendicular axis)
      let off = MARGIN;
      panels.forEach(p => {
        if (edge==='right')  { p.style.right =off+'px'; off+=p.offsetWidth +GAP; }
        if (edge==='left')   { p.style.left  =off+'px'; off+=p.offsetWidth +GAP; }
        if (edge==='bottom') { p.style.bottom=off+'px'; off+=p.offsetHeight+GAP; }
        if (edge==='top')    { p.style.top   =off+'px'; off+=p.offsetHeight+GAP; }
      });
    });
  });
}

// Generic drag – works on the panel itself, skipping interactive children
function makeDraggable(panelEl) {
  let active=false, startX, startY, origLeft, origTop;

  panelEl.addEventListener('pointerdown', e=>{
    if(!e.target.closest('.drag-handle')) return;
    e.preventDefault();
    e.stopPropagation();
    active=true;
    panelEl.setPointerCapture(e.pointerId);
    const r=panelEl.getBoundingClientRect();
    origLeft=r.left; origTop=r.top;
    startX=e.clientX; startY=e.clientY;
    // Preserve flex-direction before removing edge classes
    const curEdge=panelEl.dataset.edge;
    const initVert=curEdge==='left'||curEdge==='right';
    panelEl.classList.remove('edge-left','edge-right','edge-top','edge-bottom');
    panelEl.dataset.edge='float';
    panelEl.style.left=origLeft+'px'; panelEl.style.top=origTop+'px';
    panelEl.style.right=''; panelEl.style.bottom=''; panelEl.style.transform='none';
    panelEl.style.flexDirection=initVert?'column':'row';
    // Trigger reposition so remaining panels fill the gap
    repositionPanels();
  });

  panelEl.addEventListener('pointermove', e=>{
    if(!active) return;
    const newLeft=origLeft+e.clientX-startX;
    const newTop =origTop +e.clientY-startY;
    panelEl.style.left=newLeft+'px';
    panelEl.style.top =newTop+'px';
    // Dynamic orientation: follow nearest edge in real time
    const cx=newLeft+panelEl.offsetWidth/2, cy=newTop+panelEl.offsetHeight/2;
    const W=window.innerWidth, H=window.innerHeight;
    const d={left:cx,right:W-cx,top:cy,bottom:H-cy};
    const nearest=Object.keys(d).reduce((a,b)=>d[a]<d[b]?a:b);
    panelEl.style.flexDirection=(nearest==='left'||nearest==='right')?'column':'row';
  });

  panelEl.addEventListener('pointerup', e=>{
    if(!active) return;
    active=false;
    snapToZone(panelEl);
  });

  panelEl.addEventListener('pointercancel',()=>{ active=false; });
}

makeDraggable(toolbar);
makeDraggable(palettePanel);
makeDraggable(tabPanel);
makeDraggable(historyPanel);
makeDraggable(canvasPanel);

// ─── Tool selection ──────────────────────────────────────────────────────────
function selectTool(tool) {
  if ((state.activeTool==='select'||state.activeTool==='touch') && tool!=='select' && tool!=='touch') clearSelection();
  if (SHAPE_TOOLS.has(state.activeTool) && !SHAPE_TOOLS.has(tool)) cancelPolyShape();
  if (textEdit.active) confirmText();
  // Cancel in-progress eraser gestures when switching tools
  eraserActive=false; eraserPointerPos=null; lassoEraserPts=null;
  state.activeTool=tool;
  document.querySelectorAll('.tool-btn').forEach(b=>b.classList.remove('active-tool'));
  if (!SHAPE_TOOLS.has(tool)) document.getElementById('btn-'+tool)?.classList.add('active-tool');
  // Shapes toggle button: update icon when shape selected (icon persists when leaving)
  const toggleBtn = document.getElementById('btn-shapes-toggle');
  toggleBtn.classList.toggle('active-tool', SHAPE_TOOLS.has(tool));
  if (SHAPE_TOOLS.has(tool)) {
    lastShapeTool = tool;
    if (tool === 'regularPolygon') {
      toggleBtn.innerHTML = makeRegPolyIcon(ss.regularPolySides);
    } else {
      const spBtn = document.querySelector(`.sp-btn[data-shape="${tool}"]`);
      if (spBtn) toggleBtn.innerHTML = spBtn.querySelector('svg').outerHTML;
    }
  }
  // Eraser toggle button: update icon when eraser selected (icon persists)
  const eraserToggleBtn = document.getElementById('btn-eraser-toggle');
  if (eraserToggleBtn) {
    eraserToggleBtn.classList.toggle('active-tool', ERASER_TOOLS.has(tool));
    if (ERASER_TOOLS.has(tool)) {
      lastEraserTool = tool;
      const epBtn = document.querySelector(`.ep-btn[data-eraser="${tool}"]`);
      if (epBtn) eraserToggleBtn.innerHTML = epBtn.querySelector('svg').outerHTML;
    }
  }
  // Active eraser button highlight in panel
  document.querySelectorAll('.ep-btn').forEach(b=>b.classList.remove('active-eraser'));
  const activeEpBtn = document.querySelector(`.ep-btn[data-eraser="${tool}"]`);
  if (activeEpBtn) activeEpBtn.classList.add('active-eraser');
  // Show sides control only when regularPolygon is active
  document.getElementById('rp-popup').style.display = tool === 'regularPolygon' ? 'flex' : 'none';
  // Point eraser size popup
  const pePopup = document.getElementById('point-eraser-popup');
  if (pePopup) pePopup.style.display = tool === 'pointEraser' ? 'flex' : 'none';
  // Canvas cursor
  canvas.style.cursor = tool === 'pointEraser' ? 'none' : tool === 'touch' ? 'grab' : 'crosshair';
  // Width button: visible for all tools except laser
  closeWidthPopover();
  // Highlight active shape button in panel
  document.querySelectorAll('.sp-btn').forEach(b=>b.classList.remove('active-shape'));
  const spBtn = document.querySelector(`.sp-btn[data-shape="${tool}"]`);
  if (spBtn) spBtn.classList.add('active-shape');
  // Active shape label
  const lbl = document.getElementById('sp-active-label');
  if (lbl) lbl.textContent = SHAPE_TOOLS.has(tool) ? tool : '';
  { const key=toolWidthKey(); _syncWidthUI(key, getRawWidth(key)); }
  renderPalette();
}
document.getElementById('btn-pencil').addEventListener('click',()=>selectTool('pencil'));
document.getElementById('btn-highlighter').addEventListener('click',()=>selectTool('highlighter'));
document.getElementById('btn-laser').addEventListener('click',()=>selectTool('laser'));
document.getElementById('btn-select').addEventListener('click',()=>selectTool('select'));
document.getElementById('btn-touch').addEventListener('click',()=>selectTool('touch'));

// Group memory: last selected tool per submenu group
let lastShapeTool  = 'line';
let lastEraserTool = 'pointEraser';
let shapesPanelOpen  = false;
let eraserPanelOpen  = false;

function openShapesPanel() {
  const btn  = document.getElementById('btn-shapes-toggle');
  const br   = btn.getBoundingClientRect();
  const edge = toolbar.dataset.edge || 'right';
  const panel = document.getElementById('shapes-panel');
  panel.style.cssText = 'display:flex;flex-direction:column;';
  if (edge==='right')  { panel.style.right=(window.innerWidth-br.left+8)+'px'; panel.style.top=Math.max(8,br.top)+'px'; }
  if (edge==='left')   { panel.style.left=(br.right+8)+'px'; panel.style.top=Math.max(8,br.top)+'px'; }
  if (edge==='top')    { panel.style.top=(br.bottom+8)+'px'; panel.style.left=Math.max(8,br.left)+'px'; }
  if (edge==='bottom') { panel.style.bottom=(window.innerHeight-br.top+8)+'px'; panel.style.left=Math.max(8,br.left)+'px'; }
  shapesPanelOpen = true;
}
function closeShapesPanel() {
  document.getElementById('shapes-panel').style.display='none';
  shapesPanelOpen = false;
}
document.getElementById('btn-shapes-toggle').addEventListener('click', e => {
  e.stopPropagation();
  if (SHAPE_TOOLS.has(state.activeTool)) {
    shapesPanelOpen ? closeShapesPanel() : openShapesPanel();
  } else {
    selectTool(lastShapeTool);
    closeShapesPanel();
  }
});
document.addEventListener('pointerdown', e => {
  const panel = document.getElementById('shapes-panel');
  if (shapesPanelOpen && !panel.contains(e.target) && e.target.id !== 'btn-shapes-toggle') closeShapesPanel();
});

// Shape buttons in panel
document.querySelectorAll('.sp-btn').forEach(btn => {
  btn.addEventListener('click', e => {
    e.stopPropagation();
    selectTool(btn.dataset.shape);
    closeShapesPanel();
  });
});

// ─── Eraser panel ────────────────────────────────────────────────────────────
function openEraserPanel() {
  const btn  = document.getElementById('btn-eraser-toggle');
  const br   = btn.getBoundingClientRect();
  const edge = toolbar.dataset.edge || 'right';
  const panel = document.getElementById('eraser-panel');
  panel.style.cssText = 'display:flex;flex-direction:column;';
  if (edge==='right')  { panel.style.right=(window.innerWidth-br.left+8)+'px'; panel.style.top=Math.max(8,br.top)+'px'; }
  if (edge==='left')   { panel.style.left=(br.right+8)+'px'; panel.style.top=Math.max(8,br.top)+'px'; }
  if (edge==='top')    { panel.style.top=(br.bottom+8)+'px'; panel.style.left=Math.max(8,br.left)+'px'; }
  if (edge==='bottom') { panel.style.bottom=(window.innerHeight-br.top+8)+'px'; panel.style.left=Math.max(8,br.left)+'px'; }
  eraserPanelOpen = true;
}
function closeEraserPanel() {
  document.getElementById('eraser-panel').style.display = 'none';
  eraserPanelOpen = false;
}
document.getElementById('btn-eraser-toggle').addEventListener('click', e => {
  e.stopPropagation();
  if (ERASER_TOOLS.has(state.activeTool)) {
    eraserPanelOpen ? closeEraserPanel() : openEraserPanel();
  } else {
    selectTool(lastEraserTool);
    closeEraserPanel();
  }
});
document.addEventListener('pointerdown', e => {
  const panel = document.getElementById('eraser-panel');
  const pePopupEl = document.getElementById('point-eraser-popup');
  if (eraserPanelOpen && !panel.contains(e.target) && e.target.id !== 'btn-eraser-toggle' && !(pePopupEl && pePopupEl.contains(e.target))) closeEraserPanel();
});
document.querySelectorAll('.ep-btn').forEach(btn => {
  btn.addEventListener('click', e => {
    e.stopPropagation();
    selectTool(btn.dataset.eraser);
    closeEraserPanel();
  });
});

// ─── Point eraser size popup ──────────────────────────────────────────────────
function updatePeUI() {
  document.getElementById('pe-size-label').textContent = pointEraserR;
  state.dirty = true;
}
document.getElementById('btn-pe-minus').addEventListener('click', () => {
  pointEraserR = Math.max(4, pointEraserR - 4); updatePeUI();
});
document.getElementById('btn-pe-plus').addEventListener('click', () => {
  pointEraserR = Math.min(100, pointEraserR + 4); updatePeUI();
});

// Straighten toggle
document.getElementById('btn-straight').addEventListener('click', () => {
  state.straighten = !state.straighten;
  document.getElementById('btn-straight').classList.toggle('straight-on', state.straighten);
});

// ─── Text tool ───────────────────────────────────────────────────────────────
let shapeIdSeqText = 0;

function currentTextFontSize() {
  return getRawWidth('text');
}

function showTextOverlay(wx, wy, existingShape) {
  const fontSize = existingShape ? existingShape.fontSize : currentTextFontSize();
  const screenPx = fontSize * tab().transform.scale;
  const sp = worldToScreen(wx, wy);

  const overlay = document.getElementById('text-overlay');
  const input   = document.getElementById('text-input');

  overlay.style.left = sp.x + 'px';
  overlay.style.top  = sp.y + 'px';
  overlay.style.display = 'block';

  input.style.fontSize   = screenPx + 'px';
  input.style.lineHeight = '1.25';
  input.style.color      = state.activeColor;
  input.style.width      = '120px';
  input.style.height     = screenPx * 1.25 + 'px';
  input.value = existingShape ? existingShape.content : '';

  textEdit.active = true;
  textEdit.editingShape = existingShape || null;
  textEdit.wx = wx; textEdit.wy = wy;

  requestAnimationFrame(() => { input.focus(); autoResizeTextInput(); });
}

function autoResizeTextInput() {
  const input = document.getElementById('text-input');
  const fontSize = parseFloat(input.style.fontSize) || 20;
  const lh = fontSize * 1.25;
  const lines = input.value.split('\n');
  ctx.save();
  ctx.font = `${fontSize}px system-ui,-apple-system,sans-serif`;
  const maxW = Math.max(16, ...lines.map(l => ctx.measureText(l || '').width));
  ctx.restore();
  input.style.width  = (maxW + fontSize * 0.6) + 'px'; // +0.6em room for caret
  input.style.height = Math.max(lh, lines.length * lh) + 'px';
}

function confirmText() {
  if (!textEdit.active) return;
  const input   = document.getElementById('text-input');
  const content = input.value.trim();
  textEdit.active = false;
  document.getElementById('text-overlay').style.display = 'none';
  input.value = '';

  if (!content) {
    if (textEdit.editingShape) {
      // Delete empty edited shape
      pushUndo();
      const i = tab().shapes.indexOf(textEdit.editingShape);
      if (i !== -1) tab().shapes.splice(i, 1);
    }
    textEdit.editingShape = null;
    state.dirty = true;
    return;
  }

  const fontSize = textEdit.editingShape ? textEdit.editingShape.fontSize : currentTextFontSize();

  if (textEdit.editingShape) {
    pushUndo();
    const old = textEdit.editingShape, edited = {...old, content};
    const i = tab().shapes.indexOf(old); if (i !== -1) tab().shapes[i] = edited;
    if (sel.items) { const j = sel.items.shapes.indexOf(old); if (j !== -1) sel.items.shapes[j] = edited; }
    itemsChanged(null);
  } else {
    pushUndo();
    tab().shapes.push({
      type: 'text', id: 'tx' + (++shapeIdSeqText),
      x: textEdit.wx, y: textEdit.wy,
      content, fontSize,
      strokeColor: state.activeColor, strokeWidth: 0,
      seq: ++tab().seq,
    });
  }
  textEdit.editingShape = null;
  state.dirty = true;
}

function cancelText() {
  if (!textEdit.active) return;
  textEdit.active = false;
  textEdit.editingShape = null;
  document.getElementById('text-overlay').style.display = 'none';
  document.getElementById('text-input').value = '';
  state.dirty = true;
}

function textToolDown(e) {
  if (textEdit.active) confirmText();
  const sx = e.clientX, sy = e.clientY;
  const wx = toWorld(sx, sy).x, wy = toWorld(sx, sy).y;
  // Tap on existing text → re-edit it
  const hit = tab().shapes.find(s => s.type === 'text' && hitTestShape(s, sx, sy));
  if (hit) {
    showTextOverlay(hit.x, hit.y, hit);
  } else {
    showTextOverlay(wx, wy, null);
  }
}

// Text input events
document.getElementById('text-input').addEventListener('input', autoResizeTextInput);
document.getElementById('text-input').addEventListener('keydown', e => {
  if (e.key === 'Escape') { e.preventDefault(); cancelText(); }
  if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); confirmText(); }
});
// Stop pointer events from reaching canvas while typing
document.getElementById('text-overlay').addEventListener('pointerdown', e => e.stopPropagation());

document.getElementById('btn-text').addEventListener('click', () => selectTool('text'));

// ─── Stroke width ────────────────────────────────────────────────────────────
const widthSlider  = document.getElementById('width-slider');
const widthLabel   = document.getElementById('width-label');
const widthPopover = document.getElementById('width-popover');
const wdotCtx      = document.getElementById('width-dot').getContext('2d');
let   wpOpen       = false;

function stepsForTool(tool){ return tool==='highlighter' ? HL_WIDTH_STEPS : tool==='text' ? TEXT_SIZES : WIDTH_STEPS; }
function toolWidthKey(){ return SHAPE_TOOLS.has(state.activeTool) ? 'shape' : state.activeTool; }
function getWidthIdx(){ return tab().toolWidths[toolWidthKey()]??3; }

function getRawWidth(key){
  const t = tab();
  if (t.toolWidthPx && t.toolWidthPx[key] != null) return t.toolWidthPx[key];
  const steps = stepsForTool(key);
  return steps[t.toolWidths[key] ?? 3];
}

function _syncWidthUI(key, px){
  const steps = stepsForTool(key);
  const nearest = steps.reduce((best, v) => Math.abs(v - px) < Math.abs(best - px) ? v : best, steps[0]);
  const i = steps.indexOf(nearest);
  tab().toolWidths[key] = i;
  widthSlider.max = steps.length - 1;
  widthSlider.value = i;
  widthLabel.textContent = px;
  wdotCtx.clearRect(0,0,20,20);
  const r = Math.min(9, px / 2);
  wdotCtx.beginPath(); wdotCtx.arc(10,10,r,0,Math.PI*2);
  wdotCtx.fillStyle='#fff'; wdotCtx.fill();
}

function setWidthIdx(idx){
  const key = toolWidthKey();
  const steps = stepsForTool(key);
  const i = Math.min(steps.length-1, Math.max(0, idx));
  const px = steps[i];
  if (!tab().toolWidthPx) tab().toolWidthPx = {};
  tab().toolWidthPx[key] = px;
  tab().toolWidths[key] = i;
  widthSlider.max = steps.length-1;
  widthSlider.value = i;
  widthLabel.textContent = px;
  wdotCtx.clearRect(0,0,20,20);
  const r = Math.min(9, px/2);
  wdotCtx.beginPath(); wdotCtx.arc(10,10,r,0,Math.PI*2);
  wdotCtx.fillStyle='#fff'; wdotCtx.fill();
}

function setWidthRaw(px){
  const key = toolWidthKey();
  const steps = stepsForTool(key);
  const clamped = Math.min(200, Math.max(1, Math.round(px)));
  if (!tab().toolWidthPx) tab().toolWidthPx = {};
  tab().toolWidthPx[key] = clamped;
  _syncWidthUI(key, clamped);
}
function openWidthPopover(){
  const btn=document.getElementById('btn-width');
  const br=btn.getBoundingClientRect();
  const edge=toolbar.dataset.edge||'right';
  widthPopover.style.cssText='position:fixed;z-index:1500;display:flex;';
  if(edge==='right')  {widthPopover.style.right=(window.innerWidth-br.left+8)+'px';widthPopover.style.top=(br.top-4)+'px';}
  if(edge==='left')   {widthPopover.style.left=(br.right+8)+'px';widthPopover.style.top=(br.top-4)+'px';}
  if(edge==='top')    {widthPopover.style.top=(br.bottom+8)+'px';widthPopover.style.left=(br.left-4)+'px';}
  if(edge==='bottom') {widthPopover.style.bottom=(window.innerHeight-br.top+8)+'px';widthPopover.style.left=(br.left-4)+'px';}
  wpOpen=true;
}
function closeWidthPopover(){ widthPopover.style.display='none'; wpOpen=false; }
document.getElementById('btn-width').addEventListener('click',e=>{
  e.stopPropagation();
  wpOpen?closeWidthPopover():openWidthPopover();
});
document.addEventListener('pointerdown',e=>{
  if(wpOpen&&!widthPopover.contains(e.target)&&e.target.id!=='btn-width') closeWidthPopover();
});
widthSlider.addEventListener('input',()=>setWidthIdx(parseInt(widthSlider.value)));
document.getElementById('btn-width-minus').addEventListener('click',()=>setWidthRaw(getRawWidth(toolWidthKey())-1));
document.getElementById('btn-width-plus').addEventListener('click',()=>setWidthRaw(getRawWidth(toolWidthKey())+1));

// ─── Regular polygon sides ────────────────────────────────────────────────────
function makeRegPolyIcon(n) {
  const r = 9, cx = 12, cy = 12, a0 = -Math.PI / 2;
  const pts = Array.from({ length: n }, (_, i) => {
    const a = a0 + (2 * Math.PI * i) / n;
    return `${(cx + r * Math.cos(a)).toFixed(1)},${(cy + r * Math.sin(a)).toFixed(1)}`;
  }).join(' ');
  return `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linejoin="round"><polygon points="${pts}"/></svg>`;
}
function updateRegPolyUI() {
  const n = ss.regularPolySides;
  document.getElementById('rp-sides-label').textContent = n;
  // Update shapes-toggle dynamic icon if regularPolygon is active
  if (state.activeTool === 'regularPolygon') {
    document.getElementById('btn-shapes-toggle').innerHTML = makeRegPolyIcon(n);
  }
}
document.getElementById('btn-rp-minus').addEventListener('click', () => {
  if (ss.regularPolySides > 3) { ss.regularPolySides--; updateRegPolyUI(); state.dirty = true; }
});
document.getElementById('btn-rp-plus').addEventListener('click', () => {
  if (ss.regularPolySides < 20) { ss.regularPolySides++; updateRegPolyUI(); state.dirty = true; }
});

// ─── Palette ──────────────────────────────────────────────────────────────────
let lastTapSlot=null, lastTapTime=0;

function buildColors(){
  if(state.activeTool==='highlighter') return [...HL_PALETTE];
  return [...(luminance(tab().bgColor)<0.5?DARK_PALETTE:LIGHT_PALETTE),...state.customColors];
}
function activeColor(){ return state.activeTool==='highlighter'?state.highlighterColor:state.activeColor; }

function renderPalette(){
  const con=document.getElementById('palette-slots');
  con.innerHTML='';
  buildColors().forEach((color,idx)=>{
    const el=document.createElement('div');
    el.className='color-slot'+(color===activeColor()?' active-color':'');
    el.style.background=color;
    el.addEventListener('pointerdown',ev=>{
      ev.stopPropagation();
      const now=Date.now();
      if(lastTapSlot===idx&&now-lastTapTime<DBL_TAP_MS){openShadePicker(color,el);lastTapSlot=null;}
      else{lastTapSlot=idx;lastTapTime=now;selectColor(color);}
    });
    con.appendChild(el);
  });
}
function selectColor(c){
  if(state.activeTool==='highlighter') state.highlighterColor=c;
  else {
    state.activeColor=c;
    if(!['pencil','highlighter'].includes(state.activeTool)&&!SHAPE_TOOLS.has(state.activeTool)) selectTool('pencil');
  }
  renderPalette();
}

// Shade picker
function openShadePicker(base,anchor){
  const picker=document.getElementById('shade-picker');
  const sw=document.getElementById('shade-swatches');
  sw.innerHTML='';
  const {h,s,l}=hexToHsl(base);
  for(let i=-4;i<=4;i++){
    const lv=Math.min(95,Math.max(5,l+i*10)),c=hslToHex(h,s,lv);
    const el=document.createElement('div');
    el.className='shade-swatch'; el.style.background=c;
    el.addEventListener('pointerdown',ev=>{ev.stopPropagation();selectColor(c);closeShadePicker();});
    sw.appendChild(el);
  }
  const r=anchor.getBoundingClientRect();
  const pe=palettePanel.dataset.edge||'right';
  picker.style.cssText='position:fixed;z-index:2000;display:block;';
  if(pe==='right')  {picker.style.right=(window.innerWidth-r.left+8)+'px';picker.style.top=r.top+'px';}
  if(pe==='left')   {picker.style.left=(r.right+8)+'px';picker.style.top=r.top+'px';}
  if(pe==='top')    {picker.style.top=(r.bottom+8)+'px';picker.style.left=r.left+'px';}
  if(pe==='bottom') {picker.style.bottom=(window.innerHeight-r.top+8)+'px';picker.style.left=r.left+'px';}
}
function closeShadePicker(){ document.getElementById('shade-picker').style.display='none'; }
document.addEventListener('pointerdown',e=>{
  if(!document.getElementById('shade-picker').contains(e.target)) closeShadePicker();
});

// ─── Custom colour picker ────────────────────────────────────────────────────
const PRESET_COLORS = [
  '#000000','#333333','#666666','#999999','#cccccc','#ffffff',
  '#ff0000','#cc0000','#ff4466','#880022','#ff88aa','#ffccdd',
  '#ff6600','#ff9900','#ffcc00','#ffee44','#aacc00','#557700',
  '#00bb00','#00aa55','#00ccaa','#00ddee','#00aaff','#0055ff',
  '#0033cc','#5500cc','#9900ee','#cc00ff','#ff00cc','#884422',
  '#3b1a08','#7b3f1a','#b5651d','#d4a96a','#f5deb3',
];

let _ccpCallback = null;

function openCustomColorPicker(anchorEl, initialColor, onPick) {
  _ccpCallback = onPick;
  const picker = document.getElementById('custom-color-picker');
  document.getElementById('ccp-native').value = initialColor || '#ffffff';
  picker.style.display = '';
  // Force layout so offsetWidth/Height are accurate
  const pw = picker.offsetWidth || 196;
  const ph = picker.offsetHeight || 210;
  const r  = anchorEl.getBoundingClientRect();
  let left = r.right + 12;
  let top  = r.top;
  if (left + pw > window.innerWidth  - 8) left = r.left - pw - 12;
  if (top  + ph > window.innerHeight - 8) top  = window.innerHeight - ph - 8;
  picker.style.left = Math.max(8, left) + 'px';
  picker.style.top  = Math.max(8, top)  + 'px';
}

function closeCustomColorPicker() {
  document.getElementById('custom-color-picker').style.display = 'none';
  _ccpCallback = null;
}

(function buildCCP() {
  const wrap = document.getElementById('ccp-swatches');
  PRESET_COLORS.forEach(c => {
    const s = document.createElement('div');
    s.className = 'ccp-swatch';
    s.style.background = c;
    s.title = c;
    s.addEventListener('click', () => {
      if (_ccpCallback) _ccpCallback(c);
      closeCustomColorPicker();
    });
    wrap.appendChild(s);
  });
  // Rainbow swatch → opens native picker
  const rb = document.createElement('div');
  rb.className = 'ccp-swatch ccp-rainbow';
  rb.title = 'Colore personalizzato…';
  rb.addEventListener('click', () => document.getElementById('ccp-native').click());
  wrap.appendChild(rb);
})();

document.getElementById('ccp-native').addEventListener('input', e => {
  if (_ccpCallback) _ccpCallback(e.target.value);
});
document.getElementById('ccp-native').addEventListener('change', () => closeCustomColorPicker());

document.addEventListener('pointerdown', e => {
  const picker = document.getElementById('custom-color-picker');
  if (picker.style.display !== 'none' && !picker.contains(e.target)) closeCustomColorPicker();
}, true);

document.getElementById('btn-add-color').addEventListener('click', e => {
  openCustomColorPicker(e.currentTarget, state.activeColor, c => {
    if (state.customColors.length >= MAX_CUSTOM) state.customColors.shift();
    state.customColors.push(c);
    selectColor(c);
    renderPalette();
  });
});

// ─── Background color ────────────────────────────────────────────────────────
document.getElementById('btn-bg').addEventListener('click', e => {
  openCustomColorPicker(e.currentTarget, tab().bgColor, c => {
    tab().bgColor = c; renderPalette(); state.dirty = true;
  });
});

// ─── Grid ────────────────────────────────────────────────────────────────────
document.getElementById('btn-grid').addEventListener('click',()=>{
  tab().gridEnabled=!tab().gridEnabled;
  document.getElementById('btn-grid').classList.toggle('active-grid',tab().gridEnabled);
  state.dirty=true;
});

// ─── Undo/Redo buttons ───────────────────────────────────────────────────────
document.getElementById('btn-undo').addEventListener('click',undo);
document.getElementById('btn-redo').addEventListener('click',redo);
document.getElementById('btn-undo2').addEventListener('click',undo);
document.getElementById('btn-redo2').addEventListener('click',redo);

// ─── Tab system ───────────────────────────────────────────────────────────────
function syncTabUI(){
  document.getElementById('tab-label').textContent=(state.activeTabIndex+1)+'/'+state.tabs.length;
  document.getElementById('btn-tab-prev').style.opacity=state.activeTabIndex>0?'1':'0.35';
  document.getElementById('btn-tab-next').style.opacity=state.activeTabIndex<state.tabs.length-1?'1':'0.35';
  document.getElementById('btn-tab-add').style.opacity=state.tabs.length<MAX_TABS?'1':'0.35';
  if (mmOpen) updateMmNavUI();
}
function switchTab(i){
  if(i<0||i>=state.tabs.length) return;
  cancelStroke(); clearSelection(); state.activeTabIndex=i; state.dirty=true;
  syncTabUI(); syncUndoUI();
  document.getElementById('btn-grid').classList.toggle('active-grid',tab().gridEnabled);
  renderPalette();
}
function addTab(){
  if(state.tabs.length>=MAX_TABS) return;
  const t=makeTab(); t.bgColor=tab().bgColor;
  state.tabs.push(t); switchTab(state.tabs.length-1);
}
document.getElementById('btn-tab-prev').addEventListener('click',()=>switchTab(state.activeTabIndex-1));
document.getElementById('btn-tab-next').addEventListener('click',()=>switchTab(state.activeTabIndex+1));
document.getElementById('btn-tab-add').addEventListener('click',addTab);

// ─── Minimap ──────────────────────────────────────────────────────────────────
const MINIMAP_W = 240, MINIMAP_H = 160;
let mmOpen = false, mmPreviewIdx = 0, mmTransform = null;

function getContentBounds(tabData) {
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  const ex = (x, y) => { x0=Math.min(x0,x); y0=Math.min(y0,y); x1=Math.max(x1,x); y1=Math.max(y1,y); };
  for (const s of [...tabData.strokes, ...tabData.highlighters])
    for (const p of s.points) ex(p.x, p.y);
  for (const sh of tabData.shapes) {
    switch (sh.type) {
      case 'circle': case 'goniometric': {
        const r = Math.hypot(sh.rp.x - sh.cx, sh.rp.y - sh.cy);
        ex(sh.cx - r, sh.cy - r); ex(sh.cx + r, sh.cy + r); break;
      }
      case 'ellipse':
        ex(sh.cx - sh.rx, sh.cy - sh.ry); ex(sh.cx + sh.rx, sh.cy + sh.ry); break;
      case 'cartesian': case 'cartesianQ1': case 'cartesianQ12':
        ex(sh.ox - sh.xl, sh.oy - sh.yu); ex(sh.ox + sh.xr, sh.oy + sh.yd); break;
      case 'text':
        ex(sh.x, sh.y); ex(sh.x + (sh.fontSize||24)*6, sh.y + (sh.fontSize||24)*1.5); break;
      default:
        if (sh.v) for (const v of sh.v) ex(v.x, v.y);
    }
  }
  if (!isFinite(x0)) return null;
  const PAD = 60;
  return { x0: x0-PAD, y0: y0-PAD, x1: x1+PAD, y1: y1+PAD };
}

function renderMinimapCanvas(tabIdx) {
  const mmCanvas = document.getElementById('minimap-canvas');
  const mmCtx = mmCanvas.getContext('2d');
  const tabData = state.tabs[tabIdx];
  mmCtx.clearRect(0, 0, MINIMAP_W, MINIMAP_H);
  mmCtx.fillStyle = tabData.bgColor;
  mmCtx.fillRect(0, 0, MINIMAP_W, MINIMAP_H);
  const bounds = getContentBounds(tabData);
  if (!bounds) { mmTransform = null; updateMinimapViewportRect(); return; }
  const cW = bounds.x1 - bounds.x0, cH = bounds.y1 - bounds.y0;
  const scale = Math.min((MINIMAP_W * 0.96) / cW, (MINIMAP_H * 0.96) / cH);
  const offX = MINIMAP_W / 2 - (bounds.x0 + cW / 2) * scale;
  const offY = MINIMAP_H / 2 - (bounds.y0 + cH / 2) * scale;
  mmTransform = { scale, offX, offY };
  // Temporarily swap ctx to draw into minimap canvas
  const realCtx = ctx;
  ctx = mmCtx;
  mmCtx.save();
  mmCtx.setTransform(scale, 0, 0, scale, offX, offY);
  tabData.highlighters.forEach(s => drawStroke(s));
  tabData.strokes.forEach(s => drawStroke(s));
  tabData.shapes.forEach(s => renderShape(s));
  mmCtx.restore();
  ctx = realCtx;
  updateMinimapViewportRect();
}

function updateMinimapViewportRect() {
  const vr = document.getElementById('minimap-viewport-rect');
  if (!vr) return;
  if (!mmTransform || mmPreviewIdx !== state.activeTabIndex) { vr.style.display = 'none'; return; }
  const t = tab().transform;
  const wx = -t.tx / t.scale, wy = -t.ty / t.scale;
  const ww = canvas.width / t.scale, wh = canvas.height / t.scale;
  const sx = wx * mmTransform.scale + mmTransform.offX;
  const sy = wy * mmTransform.scale + mmTransform.offY;
  const sw = ww * mmTransform.scale, sh = wh * mmTransform.scale;
  const l = Math.max(0, sx), t2 = Math.max(0, sy);
  const r = Math.min(MINIMAP_W, sx + sw), b = Math.min(MINIMAP_H, sy + sh);
  if (r <= l || b <= t2) { vr.style.display = 'none'; return; }
  vr.style.display = 'block';
  vr.style.left = l + 'px'; vr.style.top = t2 + 'px';
  vr.style.width = (r - l) + 'px'; vr.style.height = (b - t2) + 'px';
}

function positionMinimapPopup(clickX, clickY) {
  const popup = document.getElementById('minimap-popup');
  popup.style.left = '-9999px'; popup.style.top = '-9999px'; popup.style.display = 'flex';
  const pw = popup.offsetWidth || 256, ph = popup.offsetHeight || 220;
  let x = clickX + 14, y = clickY - ph - 14;
  if (x + pw > window.innerWidth - 8) x = clickX - pw - 14;
  if (y < 8) y = clickY + 14;
  if (y + ph > window.innerHeight - 8) y = window.innerHeight - ph - 8;
  if (x < 8) x = 8;
  popup.style.left = x + 'px'; popup.style.top = y + 'px';
}

function updateMmNavUI() {
  document.getElementById('mm-tab-label').textContent = (mmPreviewIdx+1)+'/'+state.tabs.length;
  document.getElementById('btn-mm-prev').style.opacity = mmPreviewIdx > 0 ? '1' : '0.35';
  document.getElementById('btn-mm-next').style.opacity = mmPreviewIdx < state.tabs.length-1 ? '1' : '0.35';
}

function openMinimap(clickX, clickY) {
  mmPreviewIdx = state.activeTabIndex;
  updateMmNavUI();
  positionMinimapPopup(clickX, clickY);
  renderMinimapCanvas(mmPreviewIdx);
  mmOpen = true;
}

function closeMinimap() {
  document.getElementById('minimap-popup').style.display = 'none';
  mmOpen = false;
}

document.getElementById('btn-minimap').addEventListener('click', e => {
  e.stopPropagation();
  if (mmOpen) { closeMinimap(); return; }
  const r = e.currentTarget.getBoundingClientRect();
  openMinimap(r.left + r.width / 2, r.top + r.height / 2);
});

document.getElementById('btn-mm-prev').addEventListener('click', e => {
  e.stopPropagation();
  if (mmPreviewIdx > 0) { mmPreviewIdx--; updateMmNavUI(); renderMinimapCanvas(mmPreviewIdx); }
});

document.getElementById('btn-mm-next').addEventListener('click', e => {
  e.stopPropagation();
  if (mmPreviewIdx < state.tabs.length - 1) { mmPreviewIdx++; updateMmNavUI(); renderMinimapCanvas(mmPreviewIdx); }
});

document.getElementById('minimap-canvas').addEventListener('click', e => {
  if (!mmTransform) return;
  const r = e.currentTarget.getBoundingClientRect();
  const mx = e.clientX - r.left, my = e.clientY - r.top;
  // Map minimap pixels → world coords of previewed tab's content
  const wx = (mx - mmTransform.offX) / mmTransform.scale;
  const wy = (my - mmTransform.offY) / mmTransform.scale;
  // If viewing a different tab, switch to it first
  if (mmPreviewIdx !== state.activeTabIndex) switchTab(mmPreviewIdx);
  // Center active tab's viewport on (wx, wy)
  const t = tab().transform;
  t.tx = canvas.width / 2 - wx * t.scale;
  t.ty = canvas.height / 2 - wy * t.scale;
  state.dirty = true;
  closeMinimap();
});

document.addEventListener('pointerdown', e => {
  if (!mmOpen) return;
  const popup = document.getElementById('minimap-popup');
  if (!popup.contains(e.target) && e.target.id !== 'btn-minimap') closeMinimap();
});

// ─── Selection minibar buttons ───────────────────────────────────────────────
document.getElementById('btn-sel-delete').addEventListener('click', deleteSelection);
document.getElementById('btn-sel-copy').addEventListener('click', copySelection);
document.getElementById('btn-sel-shrink').addEventListener('click', ()=>scaleSelection(0.8));
document.getElementById('btn-sel-grow').addEventListener('click', ()=>scaleSelection(1.25));

// ─── Paste FAB ───────────────────────────────────────────────────────────────
document.getElementById('paste-fab').addEventListener('click', () => {
  if (pasteMode) exitPasteMode(); else enterPasteMode();
});
// Stop FAB pointer events from leaking to canvas
document.getElementById('paste-fab').addEventListener('pointerdown', e => e.stopPropagation());

// ─── Zoom controls ───────────────────────────────────────────────────────────
const ZOOM_STEP = 1.25;

function updateZoomLabel() {
  const pct = Math.round(tab().transform.scale * 100);
  document.getElementById('zoom-label').textContent = pct + '%';
}

function applyZoom(newScale, cx, cy) {
  const t = tab().transform;
  const ns = Math.min(Math.max(newScale, 0.05), 50);
  t.tx = cx - (cx - t.tx) * (ns / t.scale);
  t.ty = cy - (cy - t.ty) * (ns / t.scale);
  t.scale = ns;
  updateZoomLabel();
  state.dirty = true;
}

document.getElementById('btn-zoom-in').addEventListener('click', () => {
  applyZoom(tab().transform.scale * ZOOM_STEP, canvas.width / 2, canvas.height / 2);
});
document.getElementById('btn-zoom-out').addEventListener('click', () => {
  applyZoom(tab().transform.scale / ZOOM_STEP, canvas.width / 2, canvas.height / 2);
});
document.getElementById('btn-zoom-reset').addEventListener('click', () => {
  applyZoom(1, canvas.width / 2, canvas.height / 2);
});

// ─── Init ────────────────────────────────────────────────────────────────────

selectTool('pencil');
renderPalette();
syncTabUI();
syncUndoUI();
repositionPanels();
updateZoomLabel();

window.addEventListener('beforeunload', e => { e.preventDefault(); e.returnValue = ''; });

