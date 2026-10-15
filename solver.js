/* ══════════════════════════════════════════════════════════════════════════
   BAINT STEP-BY-STEP PROBLEM SOLVER  (solver.js)
   Solves individual maths problems offline, with every step shown.
   baintSolve(question) -> { text, topic } or null when it is not a problem it can solve for sure.
   When unsure it returns null, so the app never gives a made-up answer.
   ══════════════════════════════════════════════════════════════════════════ */
(function(){
"use strict";

/* ---------- number helpers ---------- */
const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while(b){ const t = a % b; a = b; b = t; } return a; };
const lcm = (a, b) => (a && b) ? Math.abs(a * b) / gcd(a, b) : 0;
const SUPS = {"0":"⁰","1":"¹","2":"²","3":"³","4":"⁴","5":"⁵","6":"⁶","7":"⁷","8":"⁸","9":"⁹"};
const sup = n => String(n).split("").map(c => SUPS[c] || c).join("");
const SAFE = 1e12;
function fnum(x, dp){
  if(!isFinite(x)) return String(x);
  if(Number.isInteger(x)) return String(x);
  return x.toFixed(dp == null ? 4 : dp).replace(/0+$/, "").replace(/\.$/, "");
}
function money(x){ return x.toFixed(2); }

/* ---------- exact fractions ---------- */
function F(n, d){
  if(d === undefined) d = 1;
  if(d === 0) throw new Error("div0");
  if(d < 0){ n = -n; d = -d; }
  const g = gcd(n, d) || 1;
  n = n / g; d = d / g;
  if(Math.abs(n) > SAFE || d > SAFE) throw new Error("big");
  return {n, d};
}
const fadd = (a, b) => F(a.n * b.d + b.n * a.d, a.d * b.d);
const fsub = (a, b) => F(a.n * b.d - b.n * a.d, a.d * b.d);
const fmul = (a, b) => F(a.n * b.n, a.d * b.d);
const fdiv = (a, b) => F(a.n * b.d, a.d * b.n);
const fzero = a => a.n === 0;
const fval = a => a.n / a.d;
const fstr = a => a.d === 1 ? String(a.n) : a.n + "/" + a.d;
function fromDecimalString(s){
  const m = /^(-?)(\d*)\.?(\d*)$/.exec(s);
  if(!m || (m[2] === "" && m[3] === "")) throw new Error("num");
  const dec = m[3] || "";
  if(dec.length > 6) throw new Error("num");
  const n = parseInt((m[2] || "0") + dec, 10) * (m[1] ? -1 : 1);
  return F(n, Math.pow(10, dec.length));
}

/* ---------- polynomials in x: arrays of fractions, index = power ---------- */
const pTrim = p => { p = p.slice(); while(p.length > 1 && fzero(p[p.length - 1])) p.pop(); return p; };
const pDeg = p => pTrim(p).length - 1;
function pAdd(a, b){
  const n = Math.max(a.length, b.length), r = [];
  for(let i = 0; i < n; i++) r.push(fadd(a[i] || F(0), b[i] || F(0)));
  return pTrim(r);
}
function pScale(a, k){ return pTrim(a.map(c => fmul(c, k))); }
function pMul(a, b){
  const r = [];
  for(let i = 0; i < a.length + b.length - 1; i++) r.push(F(0));
  a.forEach((x, i) => b.forEach((y, j) => { r[i + j] = fadd(r[i + j], fmul(x, y)); }));
  const t = pTrim(r);
  if(t.length > 8) throw new Error("deg");
  return t;
}
function pPow(a, n){
  if(n < 0 || n > 6) throw new Error("pow");
  let r = [F(1)];
  for(let i = 0; i < n; i++) r = pMul(r, a);
  return r;
}
function pEval(p, x){ let r = F(0); for(let i = p.length - 1; i >= 0; i--) r = fadd(fmul(r, x), p[i]); return r; }
function termStr(c, k, v, first){
  // c: fraction coefficient, k: power
  const neg = c.n < 0, a = F(Math.abs(c.n), c.d);
  let body;
  if(k === 0) body = fstr(a);
  else {
    const vv = v + (k > 1 ? sup(k) : "");
    if(a.d === 1) body = (a.n === 1 ? "" : String(a.n)) + vv;
    else body = (a.n === 1 ? "" : a.n) + vv + "/" + a.d;
  }
  if(first) return (neg ? "-" : "") + body;
  return (neg ? " - " : " + ") + body;
}
function pStr(p, v){
  v = v || "x";
  p = pTrim(p);
  let s = "", first = true;
  for(let k = p.length - 1; k >= 0; k--){
    if(fzero(p[k])) continue;
    s += termStr(p[k], k, v, first); first = false;
  }
  return s || "0";
}

/* ---------- parser: text -> polynomial in x ---------- */
function cleanMath(str){
  return String(str).toLowerCase()
    .replace(/[\u2212\u2013\u2014]/g, "-").replace(/[×·]/g, "*").replace(/÷/g, "/")
    .replace(/²/g, "^2").replace(/³/g, "^3").replace(/⁴/g, "^4")
    .replace(/\s+/g, "");
}
function parsePoly(str){
  const s = cleanMath(str);
  if(!s) return null;
  let i = 0;
  const peek = () => s[i];
  function number(){
    const m = /^\d*\.?\d+|^\d+\.?/.exec(s.slice(i));
    if(!m) throw new Error("num");
    i += m[0].length;
    return [fromDecimalString(m[0])];
  }
  function atom(){
    const c = peek();
    if(c === "x"){ i++; return [F(0), F(1)]; }
    if(c === "("){
      i++;
      const e = expr();
      if(peek() !== ")") throw new Error("paren");
      i++;
      return e;
    }
    return number();
  }
  function power(){
    let b = atom();
    if(peek() === "^"){
      i++;
      let neg = false;
      if(peek() === "-"){ neg = true; i++; }
      const m = /^\d+/.exec(s.slice(i));
      if(!m || neg) throw new Error("exp");
      i += m[0].length;
      b = pPow(b, parseInt(m[0], 10));
    }
    return b;
  }
  function term(){
    let neg = false;
    while(peek() === "+" || peek() === "-"){ if(s[i] === "-") neg = !neg; i++; }
    let f = power();
    for(;;){
      const c = peek();
      if(c === "*"){ i++; f = pMul(f, power()); }
      else if(c === "/"){
        i++;
        const d = power();
        if(d.length !== 1 || fzero(d[0])) throw new Error("div");
        f = pScale(f, F(d[0].d, d[0].n));
      }
      else if(c === "x" || c === "(" || (c >= "0" && c <= "9") || c === ".") f = pMul(f, power());
      else break;
    }
    return neg ? pScale(f, F(-1)) : f;
  }
  function expr(){
    let t = term();
    while(peek() === "+" || peek() === "-"){
      const op = s[i++];
      const r = term();
      t = op === "+" ? pAdd(t, r) : pAdd(t, pScale(r, F(-1)));
    }
    return t;
  }
  try{
    const r = expr();
    if(i !== s.length) return null;
    return r;
  }catch(e){ return null; }
}

/* ---------- output helpers ---------- */
function steps(title, list, answer){
  let out = title;
  list.forEach((st, i) => { out += "\n\nStep " + (i + 1) + ": " + st; });
  if(answer) out += "\n\nAnswer: " + answer;
  return out;
}
function perfectSquare(n){ if(n < 0) return -1; const r = Math.round(Math.sqrt(n)); return r * r === n ? r : -1; }
function simplifySqrt(n){  // n = k² × m
  let k = 1, m = n;
  for(let f = 2; f * f <= m; f++){
    while(m % (f * f) === 0){ m /= (f * f); k *= f; }
  }
  return {k, m};
}
function sqrtStr(n){
  const s = simplifySqrt(n);
  if(s.m === 1) return String(s.k);
  return (s.k === 1 ? "" : s.k) + "√" + s.m;
}
function factorStr(n, d){          // bracket for root n/d
  const lead = d === 1 ? "x" : d + "x";
  if(n === 0) return d === 1 ? "x" : "(" + lead + ")";
  return "(" + lead + (n > 0 ? " - " + n : " + " + (-n)) + ")";
}
function intCoeffs(p){            // -> [C, B, A] integers with gcd removed (quadratic)
  const L = p.reduce((acc, c) => lcm(acc, c.d), 1);
  const ints = p.map(c => c.n * (L / c.d));
  const g = ints.reduce((acc, c) => gcd(acc, c), 0) || 1;
  return ints.map(c => c / g);
}

/* ══════════════ ALGEBRA ══════════════ */
function quadraticRoots(A, B, C){
  const D = B * B - 4 * A * C;
  return D;
}
function solveQuadratic(p){
  let [C, B, A] = intCoeffs(p);
  let note = "";
  if(A < 0){ A = -A; B = -B; C = -C; note = " (multiplied by -1 so a is positive)"; }
  const std = pStr([F(C), F(B), F(A)]) + " = 0";
  const D = B * B - 4 * A * C;
  const st = [];
  st.push("Write it in standard form ax² + bx + c = 0" + note + ".\n" + std + "\na = " + A + ", b = " + B + ", c = " + C);
  let roots = [], answer = "";
  const check = r => {
    const v = pEval([F(C), F(B), F(A)], r);
    return v.n === 0;
  };
  if(C === 0){
    const r2 = F(-B, A);
    st.push("There is no constant term, so take out x as a common factor.\nx(" + pStr([F(B), F(A)]) + ") = 0");
    st.push("Set each part to zero.\nx = 0   or   " + pStr([F(B), F(A)]) + " = 0");
    st.push("Solve the second part: x = " + fstr(r2));
    roots = fzero(r2) ? [F(0)] : [r2.n < 0 ? r2 : F(0), r2.n < 0 ? F(0) : r2];
  } else if(B === 0){
    const rhs = F(-C, A);
    st.push("There is no x term, so isolate x².\nx² = " + fstr(rhs));
    if(rhs.n < 0){
      st.push("A real number squared is never negative, so there are no real solutions.");
      const s = simplifySqrt(-rhs.n * rhs.d), den = rhs.d;
      return {text: steps("Let's solve " + std + " step by step.", st, "No real solutions (the complex solutions are x = ± " + (sqrtStr(-rhs.n * rhs.d) === "1" ? "" : sqrtStr(-rhs.n * rhs.d)) + (den === 1 ? "" : "/" + den) + " i)."), topic: "quadratic"};
    }
    const num = perfectSquare(rhs.n), den = perfectSquare(rhs.d);
    if(num >= 0 && den >= 0){
      st.push("Take the square root of both sides (remember ±).\nx = ±" + fstr(F(num, den)));
      roots = [F(num, den), F(-num, den)];
    } else {
      const v = Math.sqrt(fval(rhs));
      st.push("Take the square root of both sides (remember ±).\nx = ±√" + fstr(rhs) + " ≈ ±" + fnum(v));
      return {text: steps("Let's solve " + std + " step by step.", st, "x ≈ " + fnum(v) + " or x ≈ " + fnum(-v)), topic: "quadratic"};
    }
  } else {
    const sq = perfectSquare(D);
    st.push("Work out the discriminant D = b² − 4ac.\nD = (" + B + ")² − 4(" + A + ")(" + C + ") = " + D);
    if(D >= 0 && sq >= 0){
      const r1 = F(-B + sq, 2 * A), r2 = F(-B - sq, 2 * A);
      if(A === 1){
        st.push("D is a perfect square, so it factorises. Find two numbers that multiply to " + C + " and add to " + B + ": " + (-r1.n) + " and " + (-r2.n) + ".\n" + factorStr(r1.n, r1.d) + factorStr(r2.n, r2.d) + " = 0");
      } else {
        const k = F(A, r1.d * r2.d);
        st.push("D is a perfect square, so it factorises.\n" + (k.n === 1 && k.d === 1 ? "" : fstr(k) + " ") + factorStr(r1.n, r1.d) + factorStr(r2.n, r2.d) + " = 0");
      }
      st.push("Set each bracket to zero.\nx = " + fstr(r2) + "   or   x = " + fstr(r1) + (sq === 0 ? "   (the same root twice)" : ""));
      roots = sq === 0 ? [r1] : [r2, r1];
    } else if(D >= 0){
      const s = simplifySqrt(D);
      const v1 = (-B + Math.sqrt(D)) / (2 * A), v2 = (-B - Math.sqrt(D)) / (2 * A);
      st.push("D is positive but not a perfect square, so use the quadratic formula.\nx = (-b ± √D) ÷ 2a = (" + (-B) + " ± √" + D + ") ÷ " + (2 * A));
      let exact = "x = (" + (-B) + " ± " + (s.k === 1 ? "" : s.k) + "√" + s.m + ") ÷ " + (2 * A);
      const g = gcd(gcd(Math.abs(B), s.k), 2 * A);
      if(g > 1) exact = "x = (" + (-B / g) + " ± " + (s.k / g === 1 ? "" : s.k / g) + "√" + s.m + ") ÷ " + (2 * A / g);
      st.push("Simplify the surd: √" + D + " = " + sqrtStr(D) + ".\n" + exact);
      st.push("Work out the decimal values.\nx ≈ " + fnum(v2) + "   or   x ≈ " + fnum(v1));
      return {text: steps("Let's solve " + std + " step by step.", st, "x ≈ " + fnum(v2) + " or x ≈ " + fnum(v1) + "  (exact: " + exact.replace("x = ", "") + ")"), topic: "quadratic"};
    } else {
      const s = simplifySqrt(-D);
      const re = F(-B, 2 * A);
      st.push("D is negative, so there are no real solutions (the parabola never crosses the x-axis).");
      const im = (s.k === 1 ? "" : s.k) + (s.m === 1 ? "" : "√" + s.m);
      st.push("In complex numbers: x = " + fstr(re) + " ± (" + (im || "1") + "/" + (2 * A) + ") i");
      return {text: steps("Let's solve " + std + " step by step.", st, "No real solutions."), topic: "quadratic"};
    }
  }
  const lines = roots.map(r => "x = " + fstr(r) + (check(r) ? " ✓" : ""));
  st.push("Check by substituting back into the equation.\n" + lines.join("\n"));
  answer = roots.length === 1 ? "x = " + fstr(roots[0]) : "x = " + roots.map(fstr).join(" or x = ");
  return {text: steps("Let's solve " + std + " step by step.", st, answer), topic: "quadratic"};
}
function solveLinear(pl, pr, rawEq){
  // a x + b = c x + d
  const a = pl[1] || F(0), b = pl[0], c = pr[1] || F(0), d = pr[0];
  const st = [];
  st.push("Write the equation.\n" + rawEq);
  const hadBrackets = /\(/.test(rawEq);
  if(hadBrackets || pl.length > 2 || pr.length > 2) st.push("Expand the brackets and collect like terms.\n" + pStr(pl) + " = " + pStr(pr));
  const coef = fsub(a, c), rhs = fsub(d, b);
  if(fzero(coef)){
    return {text: steps("Let's solve this equation step by step.", st.concat(["The x terms cancel out."]), fzero(rhs) ? "True for every x (infinitely many solutions)." : "No solution."), topic: "algebra"};
  }
  if(!fzero(c) || !fzero(b)) st.push("Collect the x terms on one side and the numbers on the other.\n" + pStr([F(0), coef]) + " = " + fstr(rhs));
  const x = fdiv(rhs, coef);
  st.push("Divide both sides by " + fstr(coef) + ".\nx = " + fstr(x) + (x.d !== 1 ? " ≈ " + fnum(fval(x)) : ""));
  const L = pEval(pl, x), R = pEval(pr, x);
  st.push("Check: put x = " + fstr(x) + " back in.\nLeft side = " + fstr(L) + ", right side = " + fstr(R) + (L.n === R.n && L.d === R.d ? " ✓" : ""));
  return {text: steps("Let's solve this equation step by step.", st, "x = " + fstr(x)), topic: "algebra"};
}
function solveInequality(pl, op, pr, raw){
  const a = pl[1] || F(0), b = pl[0], c = pr[1] || F(0), d = pr[0];
  const coef = fsub(a, c), rhs = fsub(d, b);
  if(fzero(coef)) return null;
  const st = ["Write the inequality.\n" + raw];
  st.push("Treat it like an equation: collect the x terms on one side and the numbers on the other.\n" + pStr([F(0), coef]) + " " + op + " " + fstr(rhs));
  let nop = op;
  const flip = {"<": ">", ">": "<", "<=": ">=", ">=": "<="};
  if(coef.n < 0){
    nop = flip[op];
    st.push("Divide both sides by " + fstr(coef) + ". Because it is NEGATIVE, flip the inequality sign.\nx " + nop + " " + fstr(fdiv(rhs, coef)));
  } else {
    st.push("Divide both sides by " + fstr(coef) + " (positive, so the sign stays).\nx " + nop + " " + fstr(fdiv(rhs, coef)));
  }
  const bound = fdiv(rhs, coef);
  const test = nop.indexOf("<") >= 0 ? fsub(bound, F(1)) : fadd(bound, F(1));
  const ok = (() => {
    const L = fval(pEval(pl, test)), R = fval(pEval(pr, test));
    return op === "<" ? L < R : op === ">" ? L > R : op === "<=" ? L <= R : L >= R;
  })();
  st.push("Check with a test value, x = " + fstr(test) + ": the original inequality is " + (ok ? "true ✓" : "false"));
  return {text: steps("Let's solve this inequality step by step.", st, "x " + nop.replace("<=", "≤").replace(">=", "≥") + " " + fstr(bound)), topic: "inequalities"};
}
function solveSimultaneous(q){
  const parts = q.split(/\band\b|[;,]|\n/).map(s => s.trim()).filter(Boolean);
  if(parts.length !== 2) return null;
  const eqs = [];
  for(const part of parts){
    const m = /^(?:(?:solve|find|simultaneous equations?|the equations?|for x and y)\s*[:.]?\s*)*(.+)=(.+)$/.exec(cleanText(part));
    if(!m) return null;
    const l = lin2(m[1]), r = lin2(m[2]);
    if(!l || !r) return null;
    eqs.push({a: fsub(l.x, r.x), b: fsub(l.y, r.y), c: fsub(r.c, l.c), raw: part.replace(/^(solve|find)\s+/i, "")});
  }
  const [e1, e2] = eqs;
  if([e1, e2].some(e => fzero(e.a) && fzero(e.b))) return null;
  const a1 = e1.a, b1 = e1.b, c1 = e1.c, a2 = e2.a, b2 = e2.b, c2 = e2.c;
  const det = fsub(fmul(a1, b2), fmul(a2, b1));
  const eqLine = (a, b, c) => pStr([F(0), a]).replace(/^0$/, "") + (fzero(b) ? "" : (b.n < 0 ? " - " : (fzero(a) ? "" : " + ")) + (fzero(a) && b.n < 0 ? "-" : "") + pStr([F(0), F(Math.abs(b.n), b.d)]).replace(/x/g, "y")) + " = " + fstr(c);
  const st = ["Write the equations and label them.\n(1)  " + eqLine(a1, b1, c1) + "\n(2)  " + eqLine(a2, b2, c2)];
  if(fzero(det)){
    const consistent = fzero(fsub(fmul(c1, b2), fmul(c2, b1))) && fzero(fsub(fmul(a1, c2), fmul(a2, c1)));
    st.push("The two lines have the same gradient (the coefficients are in proportion).");
    return {text: steps("Let's solve the simultaneous equations step by step.", st, consistent ? "Infinitely many solutions (the equations describe the same line)." : "No solution (the lines are parallel and never meet)."), topic: "simultaneous_equations"};
  }
  // elimination with integers when possible
  let x, y;
  const ints = [a1, b1, c1, a2, b2, c2].every(f => f.d === 1);
  if(ints && !fzero(b1) && !fzero(b2)){
    const B1 = b1.n, B2 = b2.n, L = lcm(Math.abs(B1), Math.abs(B2));
    const m1 = L / Math.abs(B1), m2 = L / Math.abs(B2);
    const n1 = {a: a1.n * m1, b: B1 * m1, c: c1.n * m1}, n2 = {a: a2.n * m2, b: B2 * m2, c: c2.n * m2};
    const same = Math.sign(n1.b) === Math.sign(n2.b);
    if(m1 !== 1 || m2 !== 1){
      st.push("Make the y coefficients the same size." + (m1 !== 1 ? "\nMultiply (1) by " + m1 + ":  " + eqLine(F(n1.a), F(n1.b), F(n1.c)) : "") + (m2 !== 1 ? "\nMultiply (2) by " + m2 + ":  " + eqLine(F(n2.a), F(n2.b), F(n2.c)) : ""));
    }
    const ra = same ? n1.a - n2.a : n1.a + n2.a, rc = same ? n1.c - n2.c : n1.c + n2.c;
    st.push((same ? "Subtract" : "Add") + " the equations to eliminate y.\n" + pStr([F(0), F(ra)]) + " = " + rc);
    x = F(rc, ra);
    st.push("Solve for x.\nx = " + fstr(x));
    st.push("Substitute x = " + fstr(x) + " into equation (1) to find y.\n" + eqLine(a1, F(0), F(0)).replace(" = 0", "").replace(/x/, "(" + fstr(x) + ")") + (fzero(b1) ? "" : " + ") + "");
    y = fdiv(fsub(c1, fmul(a1, x)), b1);
    // replace the clumsy substitution line with a clear one
    const ax = fmul(a1, x), rest = fsub(c1, ax);
    const yPart = (fzero(b1) ? "0" : (b1.n < 0 ? "-" : "") + ((Math.abs(b1.n) === 1 && b1.d === 1) ? "" : fstr(F(Math.abs(b1.n), b1.d))) + "y");
    st[st.length - 1] = "Substitute x = " + fstr(x) + " into equation (1) to find y.\n" + fstr(a1) + " × " + (x.n < 0 ? "(" + fstr(x) + ")" : fstr(x)) + " + " + (b1.n < 0 ? "(" + fstr(b1) + ")y" : fstr(b1) + "y") + " = " + fstr(c1) + "\n" + fstr(ax) + " " + (b1.n < 0 ? "-" : "+") + " " + ((Math.abs(b1.n) === 1 && b1.d === 1) ? "" : fstr(F(Math.abs(b1.n), b1.d))) + "y = " + fstr(c1) + (((Math.abs(b1.n) === 1 && b1.d === 1) && b1.n > 0) ? "" : "\n" + yPart + " = " + fstr(rest)) + "\ny = " + fstr(y);
  } else {
    // exact solution by Cramer's rule, explained simply
    x = fdiv(fsub(fmul(c1, b2), fmul(c2, b1)), det);
    y = fdiv(fsub(fmul(a1, c2), fmul(a2, c1)), det);
    st.push("Eliminate one unknown (multiply the equations so one variable has matching coefficients, then add or subtract).");
    st.push("This gives x = " + fstr(x) + " and y = " + fstr(y) + ".");
  }
  const ok1 = fadd(fmul(a1, x), fmul(b1, y)), ok2 = fadd(fmul(a2, x), fmul(b2, y));
  st.push("Check both equations.\n(1) " + fstr(ok1) + " = " + fstr(c1) + (ok1.n === c1.n && ok1.d === c1.d ? " ✓" : "") + "\n(2) " + fstr(ok2) + " = " + fstr(c2) + (ok2.n === c2.n && ok2.d === c2.d ? " ✓" : ""));
  return {text: steps("Let's solve the simultaneous equations step by step.", st, "x = " + fstr(x) + ", y = " + fstr(y)), topic: "simultaneous_equations"};
}
function lin2(str){            // linear expression in x and y -> {x, y, c}
  const s = cleanMath(str);
  if(!s || /[^0-9xy+\-.*\/()]/.test(s)) return null;
  const re = /([+-]?)((?:\d*\.?\d+(?:\/\d+)?)?)(\*?)([xy]?)/g;
  let pos = 0, res = {x: F(0), y: F(0), c: F(0)};
  if(/[()]/.test(s)) return null;
  while(pos < s.length){
    re.lastIndex = pos;
    const m = re.exec(s);
    if(!m || m[0] === "" || m.index !== pos) return null;
    pos += m[0].length;
    let coef;
    try{
      if(m[2] === "") coef = F(1);
      else if(m[2].indexOf("/") >= 0){ const [n, d] = m[2].split("/"); coef = fdiv(fromDecimalString(n), fromDecimalString(d)); }
      else coef = fromDecimalString(m[2]);
    }catch(e){ return null; }
    if(m[1] === "-") coef = fmul(coef, F(-1));
    if(m[4] === "") { if(m[2] === "") return null; res.c = fadd(res.c, coef); }
    else res[m[4]] = fadd(res[m[4]], coef);
  }
  return res;
}
function cleanText(s){ return String(s).replace(/[\u2212\u2013\u2014]/g, "-"); }

function factorise(p){
  p = pTrim(p);
  const deg = p.length - 1;
  if(deg < 1 || deg > 2) return null;
  const ints = intCoeffs(p);
  // restore the original scale/sign: find k with p = k * ints
  let lead = p[deg];
  let k = fdiv(lead, F(ints[deg]));
  const orig = pStr(p);
  const st = [];
  const inner = ints.map(c => F(c));
  let kStr = fstr(k);
  const hasK = !(k.n === 1 && k.d === 1);
  if(deg === 1){
    if(!hasK) return {text: steps("Let's factorise " + orig + " step by step.", ["The terms have no common factor, so it cannot be factorised further."], orig), topic: "factorisation"};
    st.push("Take out the common factor " + kStr + ".");
    return {text: steps("Let's factorise " + orig + " step by step.", st.concat(["Check by expanding: " + kStr + "(" + pStr(inner) + ") = " + orig + " ✓"]), kStr + "(" + pStr(inner) + ")"), topic: "factorisation"};
  }
  let [C, B, A] = ints;
  if(hasK) st.push("Take out the common factor " + kStr + ".\n" + kStr + "(" + pStr(inner) + ")");
  const pre = hasK ? kStr : "";
  const wrap = body => pre ? pre + body : body;
  let ans;
  if(C === 0){
    st.push("There is no constant term, so take out x.\n" + (pre ? pre : "") + "x(" + pStr([F(B), F(A)]) + ")");
    ans = (pre || "") + "x(" + pStr([F(B), F(A)]) + ")";
  } else if(B === 0 && A > 0 && perfectSquare(A) >= 0 && C < 0 && perfectSquare(-C) >= 0){
    const s = perfectSquare(A), t = perfectSquare(-C);
    st.push("This is a difference of two squares: a² − b² = (a − b)(a + b).\n" + (s === 1 ? "x" : s + "x") + "² − " + t + "²");
    ans = wrap("(" + (s === 1 ? "x" : s + "x") + " - " + t + ")(" + (s === 1 ? "x" : s + "x") + " + " + t + ")");
    st.push("Write the factors.\n" + ans);
  } else {
    const D = B * B - 4 * A * C, sq = perfectSquare(D);
    if(sq < 0){
      st.push("Check the discriminant: b² − 4ac = " + D + (D < 0 ? " (negative)" : " (not a perfect square)") + ".\nThis quadratic does not factorise using whole numbers.");
      return {text: steps("Let's factorise " + orig + " step by step.", st, "It does not factorise using whole numbers. (Use the quadratic formula to find its roots.)"), topic: "factorisation"};
    }
    const r1 = F(-B + sq, 2 * A), r2 = F(-B - sq, 2 * A);
    if(A === 1) st.push("Find two numbers that multiply to " + C + " and add to " + B + ".\nThey are " + (-r1.n) + " and " + (-r2.n) + ".");
    else st.push("Find the roots (using the quadratic formula or trial): x = " + fstr(r1) + " and x = " + fstr(r2) + ".");
    const lead2 = F(A, r1.d * r2.d);
    ans = wrap((lead2.n === 1 && lead2.d === 1 ? "" : fstr(lead2)) + factorStr(r1.n, r1.d) + factorStr(r2.n, r2.d));
    st.push("Write the factors.\n" + ans);
  }
  st.push("Check by expanding the brackets: you get back " + orig + " ✓");
  return {text: steps("Let's factorise " + orig + " step by step.", st, ans), topic: "factorisation"};
}
function expandText(str){
  const s = cleanMath(str);
  const m = /^\(([^()]+)\)\(([^()]+)\)$/.exec(s);
  const p = parsePoly(str);
  if(!p) return null;
  const st = [];
  if(m){
    const a = parsePoly(m[1]), b = parsePoly(m[2]);
    if(a && b && a.length <= 3 && b.length <= 3){
      const prods = [];
      for(let i = a.length - 1; i >= 0; i--) for(let j = b.length - 1; j >= 0; j--) prods.push(pStr([...Array(i + j).fill(F(0)), fmul(a[i], b[j])]));
      st.push("Multiply every term in the first bracket by every term in the second.\n" + prods.join(" , "));
      st.push("Add them up and collect like terms.\n" + pStr(p));
      return {text: steps("Let's expand (" + pStr(a) + ")(" + pStr(b) + ") step by step.", st, pStr(p)), topic: "factorisation"};
    }
  }
  st.push("Multiply out the brackets, then collect like terms.");
  return {text: steps("Let's expand " + str.trim() + " step by step.", st, pStr(p)), topic: "factorisation"};
}

/* ══════════════ CALCULUS (polynomials and a few standard functions) ══════════════ */
function ratCoefStr(c, k, v){      // fraction coefficient with power
  return termStr(c, k, v, true);
}
function differentiate(p){
  const st = [];
  const terms = [];
  const res = [];
  for(let k = 0; k < p.length; k++){
    if(fzero(p[k])) continue;
    if(k === 0){ terms.push("The derivative of the constant " + fstr(p[0]) + " is 0."); res.push(F(0)); continue; }
    const nc = fmul(p[k], F(k));
    terms.push("d/dx of " + termStr(p[k], k, "x", true) + " → " + k + " × " + fstr(p[k]) + (k - 1 === 0 ? "" : "x" + (k - 1 > 1 ? sup(k - 1) : "")) + " = " + termStr(nc, k - 1, "x", true));
    res[k - 1] = nc;
  }
  for(let i = 0; i < p.length - 1; i++) res[i] = res[i] || F(0);
  const dp = pTrim(res.length ? res.map(c => c || F(0)) : [F(0)]);
  st.push("Use the power rule: the derivative of axⁿ is n·a·xⁿ⁻¹. Differentiate term by term.\n" + terms.join("\n"));
  st.push("Add the results.\n" + pStr(dp));
  return {text: steps("Let's differentiate " + pStr(p) + " step by step.", st, "dy/dx = " + pStr(dp)), topic: "derivatives"};
}
function integrate(p, lo, hi){
  const st = [];
  const terms = [];
  const res = [F(0)];
  for(let k = 0; k < p.length; k++){
    if(fzero(p[k])) continue;
    const nc = fdiv(p[k], F(k + 1));
    terms.push(termStr(p[k], k, "x", true) + " → " + termStr(nc, k + 1, "x", true));
    res[k + 1] = nc;
  }
  for(let i = 0; i < res.length; i++) res[i] = res[i] || F(0);
  const ip = pTrim(res);
  st.push("Use the power rule for integration: the integral of axⁿ is a·xⁿ⁺¹ ÷ (n + 1). Integrate term by term.\n" + terms.join("\n"));
  if(lo === undefined){
    st.push("Add the constant of integration C.\n" + pStr(ip) + " + C");
    return {text: steps("Let's integrate " + pStr(p) + " step by step.", st, pStr(ip) + " + C"), topic: "integrals"};
  }
  const Fb = pEval(ip, hi), Fa = pEval(ip, lo);
  st.push("Substitute the limits: F(" + fstr(hi) + ") − F(" + fstr(lo) + ").\nF(" + fstr(hi) + ") = " + fstr(Fb) + "\nF(" + fstr(lo) + ") = " + fstr(Fa));
  const val = fsub(Fb, Fa);
  st.push("Subtract.\n" + fstr(Fb) + " − " + (Fa.n < 0 ? "(" + fstr(Fa) + ")" : fstr(Fa)) + " = " + fstr(val) + (val.d !== 1 ? " ≈ " + fnum(fval(val)) : ""));
  return {text: steps("Let's find the definite integral of " + pStr(p) + " from " + fstr(lo) + " to " + fstr(hi) + ".", st, fstr(val) + (val.d !== 1 ? " ≈ " + fnum(fval(val)) : "")), topic: "integrals"};
}
const STD_DERIV = {"sin x": ["cos x", "The derivative of sin x is cos x."], "cos x": ["-sin x", "The derivative of cos x is -sin x."], "tan x": ["sec²x", "The derivative of tan x is sec²x."], "e^x": ["e^x", "The derivative of eˣ is eˣ."], "ln x": ["1/x", "The derivative of ln x is 1/x."]};
const STD_INTEG = {"sin x": ["-cos x + C", "The integral of sin x is -cos x."], "cos x": ["sin x + C", "The integral of cos x is sin x."], "e^x": ["e^x + C", "The integral of eˣ is eˣ."], "1/x": ["ln|x| + C", "The integral of 1/x is ln|x|."]};

/* ══════════════ NUMBERS AND ARITHMETIC TOPICS ══════════════ */
function roots(q){
  let m = /(?:square\s*root|sqrt|√)\s*(?:of\s*)?\(?\s*(\d+(?:\.\d+)?)\s*\)?/.exec(q);
  if(m){
    const n = parseFloat(m[1]);
    if(Number.isInteger(n)){
      const s = simplifySqrt(n), r = Math.sqrt(n);
      const st = [];
      if(s.m === 1) { st.push("Ask: which number multiplied by itself gives " + n + "?\n" + s.k + " × " + s.k + " = " + n); return {text: steps("Let's find the square root of " + n + ".", st, "√" + n + " = " + s.k), topic: "exponents"}; }
      st.push("Look for the biggest square number that divides " + n + ".\n" + n + " = " + (s.k * s.k) + " × " + s.m);
      if(s.k > 1) st.push("Take the square root of the square part.\n√" + n + " = " + s.k + "√" + s.m);
      st.push("As a decimal: √" + n + " ≈ " + fnum(r));
      return {text: steps("Let's find the square root of " + n + ".", st, (s.k > 1 ? s.k + "√" + s.m + " ≈ " : "√" + n + " ≈ ") + fnum(r)), topic: "surds"};
    }
    return {text: steps("Let's find the square root of " + n + ".", ["Use a calculator or estimate between two square numbers."], "√" + n + " ≈ " + fnum(Math.sqrt(n))), topic: "exponents"};
  }
  m = /(?:cube\s*root|∛)\s*(?:of\s*)?(\d+)/.exec(q);
  if(m){
    const n = parseInt(m[1], 10), r = Math.round(Math.cbrt(n));
    if(r * r * r === n) return {text: steps("Let's find the cube root of " + n + ".", ["Ask: which number multiplied by itself three times gives " + n + "?\n" + r + " × " + r + " × " + r + " = " + n], "∛" + n + " = " + r), topic: "exponents"};
    return {text: steps("Let's find the cube root of " + n + ".", ["It is not a whole number, so estimate between two cubes."], "∛" + n + " ≈ " + fnum(Math.cbrt(n))), topic: "exponents"};
  }
  return null;
}
function factorial(q){
  const m = /(?:^|\b)(\d{1,2})\s*(?:!|factorial)(?!\w*=)/.exec(q) || /factorial\s*(?:of\s*)?(\d{1,2})\b/.exec(q);
  if(!m) return null;
  const n = parseInt(m[1], 10);
  if(n > 20) return null;
  let r = 1; const parts = [];
  for(let i = n; i >= 1; i--){ r *= i; parts.push(i); }
  const st = ["n! means multiply every whole number from n down to 1.\n" + n + "! = " + (parts.join(" × ") || "1")];
  const run = []; let acc = 1;
  for(let i = n; i >= 1; i--){ acc *= i; run.push(acc); }
  if(n > 2) st.push("Multiply step by step: " + run.join(" → "));
  if(n === 0) st.push("By definition, 0! = 1.");
  return {text: steps("Let's work out " + n + "!", st, n + "! = " + r), topic: "permutations_combinations"};
}
function logarithm(q){
  let m = /\blog\s*(?:base\s*)?(\d+(?:\.\d+)?)\s+(?:of\s+)?(\d+(?:\.\d+)?)\b/.exec(q);
  let base, val;
  if(m){ base = parseFloat(m[1]); val = parseFloat(m[2]); }
  else {
    m = /\blog\s*(?:of\s*)?(\d+(?:\.\d+)?)\b/.exec(q);
    if(!m) return null;
    base = 10; val = parseFloat(m[1]);
  }
  if(base <= 0 || base === 1 || val <= 0) return null;
  const y = Math.log(val) / Math.log(base), r = Math.round(y);
  const st = ["log" + (base === 10 ? "" : "₍" + base + "₎") + " " + val + " asks: to what power must " + base + " be raised to get " + val + "?"];
  if(Math.abs(Math.pow(base, r) - val) < 1e-9){
    st.push(base + sup(r) + " = " + val + ", so the power is " + r + ".");
    return {text: steps("Let's work out log base " + base + " of " + val + ".", st, String(r)), topic: "logarithms"};
  }
  st.push("This is not a whole-number power, so use a calculator: log(" + val + ") ÷ log(" + base + ").");
  return {text: steps("Let's work out log base " + base + " of " + val + ".", st, "≈ " + fnum(y)), topic: "logarithms"};
}
function powersSimple(q){
  const m = /^\s*(?:what is |calculate |find |evaluate )?(\d+(?:\.\d+)?)\s*(?:\^|\*\*)\s*(-?\d+)\s*\??$/.exec(q);
  if(!m) return null;
  return null;           // plain arithmetic powers are handled by the original calculator
}
function fractionTasks(q){
  let m = /simplify\s+(?:the fraction\s+)?(\d+)\s*\/\s*(\d+)/.exec(q) || /reduce\s+(\d+)\s*\/\s*(\d+)/.exec(q);
  if(m){
    const n = parseInt(m[1], 10), d = parseInt(m[2], 10);
    if(d === 0) return null;
    const g = gcd(n, d);
    const st = ["Find the highest common factor (HCF) of " + n + " and " + d + ": it is " + g + "."];
    if(g === 1) return {text: steps("Let's simplify " + n + "/" + d + ".", st.concat(["The HCF is 1, so the fraction is already in its simplest form."]), n + "/" + d), topic: "fractions"};
    st.push("Divide the top and the bottom by " + g + ".\n" + n + " ÷ " + g + " = " + n / g + "\n" + d + " ÷ " + g + " = " + d / g);
    return {text: steps("Let's simplify " + n + "/" + d + ".", st, n / g + "/" + d / g), topic: "fractions"};
  }
  m = /(?:convert|change|write|express|turn)?\s*(\d*\.\d+|\d+)\s*(?:as|to|into)\s*(?:a\s*)?fraction/.exec(q);
  if(m && /\./.test(m[1])){
    const f = fromDecimalString(m[1]);
    const dec = m[1].split(".")[1].length;
    const st = ["Write the decimal over a power of 10 (one zero for each decimal place).\n" + m[1] + " = " + m[1].replace(".", "") + "/" + Math.pow(10, dec)];
    const raw = parseInt(m[1].replace(".", ""), 10), den = Math.pow(10, dec), g = gcd(raw, den);
    if(g > 1) st.push("Simplify by dividing top and bottom by " + g + ".\n" + raw + "/" + den + " = " + fstr(f));
    return {text: steps("Let's convert " + m[1] + " to a fraction.", st, fstr(f)), topic: "decimals"};
  }
  m = /(\d+)\s*\/\s*(\d+)\s*(?:as|to|into)\s*(?:a\s*)?(decimal|percent(?:age)?)/.exec(q);
  if(m){
    const n = parseInt(m[1], 10), d = parseInt(m[2], 10);
    if(d === 0) return null;
    const v = n / d;
    if(m[3] === "decimal") return {text: steps("Let's convert " + n + "/" + d + " to a decimal.", ["A fraction means top ÷ bottom.\n" + n + " ÷ " + d + " = " + fnum(v, 6)], fnum(v, 6) + (Number.isInteger(v * 1e6) ? "" : "… (rounded)")), topic: "decimals"};
    return {text: steps("Let's convert " + n + "/" + d + " to a percentage.", ["Divide: " + n + " ÷ " + d + " = " + fnum(v, 6), "Multiply by 100: " + fnum(v, 6) + " × 100 = " + fnum(v * 100, 4) + "%"], fnum(v * 100, 4) + "%"), topic: "percentages"};
  }
  m = /(\d+(?:\.\d+)?)\s*%\s*(?:as|to|into)\s*(?:a\s*)?(fraction|decimal)/.exec(q);
  if(m){
    const p = fromDecimalString(m[1]);
    const fr = fdiv(p, F(100));
    if(m[2] === "fraction") return {text: steps("Let's convert " + m[1] + "% to a fraction.", ["Percent means 'out of 100'.\n" + m[1] + "% = " + m[1] + "/100", "Simplify.\n" + fstr(fr)], fstr(fr)), topic: "percentages"};
    return {text: steps("Let's convert " + m[1] + "% to a decimal.", ["Divide by 100.\n" + m[1] + " ÷ 100 = " + fnum(fval(fr), 6)], fnum(fval(fr), 6)), topic: "percentages"};
  }
  m = /(\d+)\s*\/\s*(\d+)\s*([+\-*×÷x\/])\s*(\d+)\s*\/\s*(\d+)/.exec(q.replace(/\s+/g, " "));
  if(m){
    const a = F(parseInt(m[1], 10), parseInt(m[2], 10)), b = F(parseInt(m[4], 10), parseInt(m[5], 10));
    const op = m[3];
    let r, st = [], name;
    if(op === "+" || op === "-"){
      const L = lcm(a.d, b.d);
      const an = a.n * (L / a.d), bn = b.n * (L / b.d);
      st.push("Use a common denominator, " + L + ".\n" + fstr(a) + " = " + an + "/" + L + " and " + fstr(b) + " = " + bn + "/" + L);
      const sn = op === "+" ? an + bn : an - bn;
      st.push((op === "+" ? "Add" : "Subtract") + " the numerators.\n" + an + " " + op + " " + bn + " = " + sn + " → " + sn + "/" + L);
      r = F(sn, L);
      if(!(r.n === sn && r.d === L)) st.push("Simplify.\n" + sn + "/" + L + " = " + fstr(r));
      name = op === "+" ? "add" : "subtract";
    } else if(op === "*" || op === "×" || op === "x"){
      st.push("Multiply the tops and multiply the bottoms.\n(" + a.n + " × " + b.n + ") / (" + a.d + " × " + b.d + ") = " + (a.n * b.n) + "/" + (a.d * b.d));
      r = fmul(a, b);
      if(!(r.n === a.n * b.n && r.d === a.d * b.d)) st.push("Simplify.\n" + fstr(r));
      name = "multiply";
    } else {
      if(b.n === 0) return null;
      st.push("To divide, flip the second fraction and multiply.\n" + fstr(a) + " × " + b.d + "/" + b.n);
      r = fdiv(a, b);
      st.push("Multiply and simplify.\n" + fstr(r));
      name = "divide";
    }
    return {text: steps("Let's " + name + " " + fstr(a) + " and " + fstr(b) + ".", st, fstr(r) + (r.d !== 1 && Math.abs(r.n) > r.d ? " = " + Math.trunc(r.n / r.d) + " " + (Math.abs(r.n) % r.d) + "/" + r.d : "")), topic: "fractions"};
  }
  return null;
}

/* ══════════════ PERCENTAGES, RATIO, INTEREST, SPEED ══════════════ */
function numIn(s){ return parseFloat(String(s).replace(/,/g, "")); }
function percentTasks(q){
  let m = /(?:increase|raise)\s*\$?(\d[\d,]*(?:\.\d+)?)\s*by\s*(\d+(?:\.\d+)?)\s*%/.exec(q) || /\$?(\d[\d,]*(?:\.\d+)?)\s*(?:is\s*)?increased\s*by\s*(\d+(?:\.\d+)?)\s*%/.exec(q);
  if(m){
    const v = numIn(m[1]), p = parseFloat(m[2]);
    const inc = v * p / 100;
    return {text: steps("Let's increase " + v + " by " + p + "%.", ["Find " + p + "% of " + v + ".\n" + p + "/100 × " + v + " = " + fnum(inc, 4), "Add it to the original.\n" + v + " + " + fnum(inc, 4) + " = " + fnum(v + inc, 4)], fnum(v + inc, 4)), topic: "percentages"};
  }
  m = /(?:decrease|reduce)\s*\$?(\d[\d,]*(?:\.\d+)?)\s*by\s*(\d+(?:\.\d+)?)\s*%/.exec(q) || /\$?(\d[\d,]*(?:\.\d+)?)\s*(?:is\s*)?(?:decreased|reduced)\s*by\s*(\d+(?:\.\d+)?)\s*%/.exec(q);
  if(m){
    const v = numIn(m[1]), p = parseFloat(m[2]);
    const dec = v * p / 100;
    return {text: steps("Let's decrease " + v + " by " + p + "%.", ["Find " + p + "% of " + v + ".\n" + p + "/100 × " + v + " = " + fnum(dec, 4), "Subtract it from the original.\n" + v + " - " + fnum(dec, 4) + " = " + fnum(v - dec, 4)], fnum(v - dec, 4)), topic: "percentages"};
  }
  m = /(?:percentage|percent)\s*(?:change|increase|decrease)\s*(?:from|between)\s*\$?(\d[\d,]*(?:\.\d+)?)\s*(?:to|and)\s*\$?(\d[\d,]*(?:\.\d+)?)/.exec(q);
  if(m){
    const a = numIn(m[1]), b = numIn(m[2]);
    if(a === 0) return null;
    const ch = b - a, pc = ch / a * 100;
    return {text: steps("Let's find the percentage change from " + a + " to " + b + ".", ["Find the change.\n" + b + " - " + a + " = " + fnum(ch, 4), "Divide by the ORIGINAL value.\n" + fnum(ch, 4) + " ÷ " + a + " = " + fnum(ch / a, 6), "Multiply by 100.\n" + fnum(pc, 4) + "%"], fnum(Math.abs(pc), 4) + "% " + (ch >= 0 ? "increase" : "decrease")), topic: "percentages"};
  }
  m = /what\s*percent(?:age)?\s*is\s*\$?(\d[\d,]*(?:\.\d+)?)\s*of\s*\$?(\d[\d,]*(?:\.\d+)?)/.exec(q) || /\$?(\d[\d,]*(?:\.\d+)?)\s*as\s*a\s*percent(?:age)?\s*of\s*\$?(\d[\d,]*(?:\.\d+)?)/.exec(q);
  if(m){
    const a = numIn(m[1]), b = numIn(m[2]);
    if(b === 0) return null;
    return {text: steps("Let's find what percentage " + a + " is of " + b + ".", ["Write it as a fraction.\n" + a + "/" + b, "Divide.\n" + a + " ÷ " + b + " = " + fnum(a / b, 6), "Multiply by 100.\n" + fnum(a / b * 100, 4) + "%"], fnum(a / b * 100, 4) + "%"), topic: "percentages"};
  }
  m = /(\d+(?:\.\d+)?)\s*%\s*(?:off|discount)/.exec(q);
  if(m){
    const nums = (q.replace(m[0], " ").match(/\$?\d[\d,]*(?:\.\d+)?/g) || []).map(x => numIn(x.replace("$", "")));
    if(nums.length === 1){
      const p = parseFloat(m[1]), price = nums[0], disc = price * p / 100;
      return {text: steps("Let's find the sale price.", ["Find the discount.\n" + p + "% of " + price + " = " + fnum(disc, 4), "Subtract it from the price.\n" + price + " - " + fnum(disc, 4) + " = " + fnum(price - disc, 4)], fnum(price - disc, 4)), topic: "percentages"};
    }
  }
  return null;
}
function ratioShare(q){
  const m = /(?:share|divide|split)\s*\$?(\d[\d,]*(?:\.\d+)?)\s*(?:in|in the ratio|into the ratio|in a ratio of|using the ratio)\s*(\d+)\s*:\s*(\d+)(?:\s*:\s*(\d+))?/.exec(q);
  if(!m) return null;
  const total = numIn(m[1]);
  const parts = [m[2], m[3], m[4]].filter(Boolean).map(Number);
  if(parts.some(p => p <= 0)) return null;
  const sum = parts.reduce((a, b) => a + b, 0), one = total / sum;
  const shares = parts.map(p => p * one);
  return {text: steps("Let's share " + total + " in the ratio " + parts.join(":") + ".", ["Add the parts of the ratio.\n" + parts.join(" + ") + " = " + sum + " parts", "Find the value of one part.\n" + total + " ÷ " + sum + " = " + fnum(one, 4), "Multiply by each part.\n" + parts.map((p, i) => p + " × " + fnum(one, 4) + " = " + fnum(shares[i], 4)).join("\n")], shares.map(s => fnum(s, 4)).join(" and ") + "  (check: they add up to " + fnum(shares.reduce((a, b) => a + b, 0), 4) + ")"), topic: "ratio_proportion"};
}
function interest(q){
  if(!/interest/.test(q)) return null;
  const compound = /compound/.test(q);
  const pm = /(?:\$|£|€)\s*(\d[\d,]*(?:\.\d+)?)|(?:on|of|for)\s*(\d[\d,]*(?:\.\d+)?)(?!\s*(?:%|years?|yrs?|months?))/.exec(q);
  const rm = /(\d+(?:\.\d+)?)\s*%/.exec(q);
  const tm = /(\d+(?:\.\d+)?)\s*(years?|yrs?|months?)/.exec(q);
  if(!pm || !rm || !tm) return null;
  const P = numIn(pm[1] || pm[2]), r = parseFloat(rm[1]) / 100;
  let t = parseFloat(tm[1]);
  if(/month/.test(tm[2])) t = t / 12;
  if(!(P > 0 && r >= 0 && t > 0)) return null;
  if(!compound){
    const I = P * r * t;
    return {text: steps("Let's find the simple interest.", ["Write the formula: I = P × r × t.\nP = " + P + ", r = " + rm[1] + "% = " + fnum(r, 6) + ", t = " + fnum(t, 4) + " years", "Substitute.\nI = " + P + " × " + fnum(r, 6) + " × " + fnum(t, 4) + " = " + money(I), "Total amount = P + I = " + P + " + " + money(I) + " = " + money(P + I)], "Interest = " + money(I) + ", total = " + money(P + I)), topic: "interest"};
  }
  if(!Number.isInteger(t)) return null;
  const A = P * Math.pow(1 + r, t);
  return {text: steps("Let's find the compound interest (compounded once a year).", ["Write the formula: A = P(1 + r)ⁿ.\nP = " + P + ", r = " + fnum(r, 6) + ", n = " + t + " years", "Substitute.\nA = " + P + " × (1 + " + fnum(r, 6) + ")" + sup(t) + " = " + P + " × " + fnum(Math.pow(1 + r, t), 6) + " = " + money(A), "Interest = A − P = " + money(A) + " − " + P + " = " + money(A - P)], "Total = " + money(A) + ", compound interest = " + money(A - P)), topic: "interest"};
}
const TIME_UNITS = "hours?|hrs?|h|minutes?|mins?|seconds?|secs?|s";
function toBase(v, unit){
  if(/^(hours?|hrs?|h)$/.test(unit)) return {v, u: "h"};
  if(/^(minutes?|mins?)$/.test(unit)) return {v, u: "min"};
  return {v, u: "s"};
}
function speedTasks(q){
  if(!/speed|distance|how fast|how far|how long|time|travel|drive|walk|run|cycle/.test(q)) return null;
  let m = new RegExp("(\\d+(?:\\.\\d+)?)\\s*(km|kilometres?|kilometers?|m|metres?|meters?|miles?)\\s*(?:in|within|takes?|taking|over)\\s*(\\d+(?:\\.\\d+)?)\\s*(" + TIME_UNITS + ")\\b").exec(q);
  if(m && /speed|how fast|average/.test(q)){
    const d = parseFloat(m[1]), t = parseFloat(m[3]);
    if(t === 0) return null;
    const du = /^k/.test(m[2]) ? "km" : /^mi/.test(m[2]) ? "miles" : "m", tu = toBase(t, m[4]).u;
    const unit = du + "/" + tu;
    return {text: steps("Let's find the speed.", ["Write the formula: speed = distance ÷ time.", "Substitute.\nspeed = " + d + " " + du + " ÷ " + t + " " + tu + " = " + fnum(d / t, 4) + " " + unit], fnum(d / t, 4) + " " + unit), topic: "speed_distance_time"};
  }
  m = new RegExp("(\\d+(?:\\.\\d+)?)\\s*(km/h|kmh|kph|mph|m/s|km per hour|miles per hour|metres per second|meters per second)\\s*(?:for|over|during)\\s*(\\d+(?:\\.\\d+)?)\\s*(" + TIME_UNITS + ")\\b").exec(q);
  if(m && /distance|how far|how many|travel|cover/.test(q)){
    const s = parseFloat(m[1]), t = parseFloat(m[3]);
    const su = /km/.test(m[2]) ? "km/h" : /mph|miles/.test(m[2]) ? "mph" : "m/s";
    const tu = toBase(t, m[4]).u;
    let tt = t;
    if(su !== "m/s" && tu === "min") tt = t / 60;
    if(su === "m/s" && tu === "h") return null;
    if(su === "m/s" && tu === "min") tt = t * 60;
    const du = su === "km/h" ? "km" : su === "mph" ? "miles" : "m";
    const conv = (tt !== t) ? "\nConvert the time so the units match: " + t + " " + tu + " = " + fnum(tt, 4) + (su === "m/s" ? " s" : " h") : "";
    return {text: steps("Let's find the distance.", ["Write the formula: distance = speed × time." + conv, "Substitute.\ndistance = " + s + " " + su + " × " + fnum(tt, 4) + " = " + fnum(s * tt, 4) + " " + du], fnum(s * tt, 4) + " " + du), topic: "speed_distance_time"};
  }
  m = /(\d+(?:\.\d+)?)\s*(km|kilometres?|kilometers?|m|metres?|meters?|miles?)\b.*?\bat\s*(\d+(?:\.\d+)?)\s*(km\/h|kmh|kph|mph|m\/s|km per hour|miles per hour|metres per second|meters per second)/.exec(q);
  if(m && /time|how long/.test(q)){
    const d = parseFloat(m[1]), s = parseFloat(m[3]);
    if(s === 0) return null;
    const tu = /m\/s|per second/.test(m[4]) ? "s" : "h";
    const du = /^k/.test(m[2]) ? "km" : /^mi/.test(m[2]) ? "miles" : "m";
    if((tu === "s" && du !== "m") || (tu === "h" && du === "m")) return null;
    const t = d / s;
    const extra = tu === "h" ? "\n(that is " + fnum(t * 60, 2) + " minutes)" : "";
    return {text: steps("Let's find the time.", ["Write the formula: time = distance ÷ speed.", "Substitute.\ntime = " + d + " " + du + " ÷ " + s + " " + m[4].replace(/per hour/, "/h") + " = " + fnum(t, 4) + " " + (tu === "h" ? "hours" : "seconds") + extra], fnum(t, 4) + " " + (tu === "h" ? "hours" : "seconds")), topic: "speed_distance_time"};
  }
  return null;
}

/* ══════════════ STATISTICS ══════════════ */
function listNumbers(q){
  const cut = q.replace(/^.*?\b(?:of|for|in|from)\b/, "");
  const m = cut.match(/-?\d+(?:\.\d+)?/g);
  return m ? m.map(Number) : [];
}
function statsTasks(q){
  if(!/\b(median|mode|range)\b/.test(q)) return null;
  const nums = listNumbers(q);
  if(nums.length < 3 || nums.length > 60) return null;
  const sorted = nums.slice().sort((a, b) => a - b), n = sorted.length;
  const out = [], st = ["Put the numbers in order, smallest to largest.\n" + sorted.join(", ")];
  const ans = [];
  if(/\bmedian\b/.test(q)){
    const med = n % 2 ? sorted[(n - 1) / 2] : (sorted[n / 2 - 1] + sorted[n / 2]) / 2;
    st.push(n % 2 ? "There are " + n + " numbers (odd), so the median is the middle one: " + fnum(med) : "There are " + n + " numbers (even), so the median is the mean of the two middle ones.\n(" + sorted[n / 2 - 1] + " + " + sorted[n / 2] + ") ÷ 2 = " + fnum(med));
    ans.push("median = " + fnum(med));
  }
  if(/\bmode\b/.test(q)){
    const cnt = {}; sorted.forEach(v => cnt[v] = (cnt[v] || 0) + 1);
    const mx = Math.max(...Object.values(cnt)), modes = Object.keys(cnt).filter(k => cnt[k] === mx);
    if(mx === 1) { st.push("No number appears more than once, so there is no mode."); ans.push("no mode"); }
    else { st.push("The mode is the number that appears most often.\n" + modes.join(" and ") + " appears " + mx + " times."); ans.push("mode = " + modes.join(" and ")); }
  }
  if(/\brange\b/.test(q)){
    const r = sorted[n - 1] - sorted[0];
    st.push("The range is the largest minus the smallest.\n" + sorted[n - 1] + " - " + sorted[0] + " = " + fnum(r));
    ans.push("range = " + fnum(r));
  }
  if(/\b(mean|average)\b/.test(q)){
    const s = sorted.reduce((a, b) => a + b, 0);
    st.push("The mean is the total divided by how many numbers.\n(" + sorted.join(" + ") + ") ÷ " + n + " = " + fnum(s) + " ÷ " + n + " = " + fnum(s / n));
    ans.unshift("mean = " + fnum(s / n));
  }
  if(!ans.length) return null;
  return {text: steps("Let's work through this data set step by step.", st, ans.join(", ")), topic: "statistics"};
}

/* ══════════════ PROBABILITY ══════════════ */
function probStr(fav, tot){
  const f = F(fav, tot);
  return fstr(f) + " = " + fnum(fav / tot, 4) + " = " + fnum(fav / tot * 100, 2) + "%";
}
function probabilityTasks(q){
  if(!/probab|chance|likel|odds/.test(q)) return null;
  let m;
  if(/\b(?:dice|die)\b|\brolling\b|\broll\b|\bthrowing\b|\bthrow\b/.test(q) && !/\bcoins?\b/.test(q) && !/\b(?:two|2|pair of)\s*(?:fair\s*)?(?:dice|die)\b/.test(q)){
    const all = [1, 2, 3, 4, 5, 6];
    let fav = null, label = "";
    if((m = /\b(?:greater|more|higher)\s*than\s*(\d)/.exec(q))){ fav = all.filter(x => x > +m[1]); label = "greater than " + m[1]; }
    else if((m = /\b(?:less|fewer|lower)\s*than\s*(\d)/.exec(q))){ fav = all.filter(x => x < +m[1]); label = "less than " + m[1]; }
    else if((m = /at\s*least\s*(?:a\s*)?(\d)/.exec(q))){ fav = all.filter(x => x >= +m[1]); label = "at least " + m[1]; }
    else if((m = /at\s*most\s*(?:a\s*)?(\d)/.exec(q))){ fav = all.filter(x => x <= +m[1]); label = "at most " + m[1]; }
    else if(/\beven\b/.test(q)){ fav = [2, 4, 6]; label = "even"; }
    else if(/\bodd\b/.test(q)){ fav = [1, 3, 5]; label = "odd"; }
    else if(/\bprime\b/.test(q)){ fav = [2, 3, 5]; label = "prime"; }
    else if(/\bnot\s*(?:a\s*|an\s*)?(\d)\b/.exec(q)){ m = /\bnot\s*(?:a\s*|an\s*)?(\d)\b/.exec(q); fav = all.filter(x => x !== +m[1]); label = "not a " + m[1]; }
    else if((m = /\b(?:a|an|getting|rolling|roll|throw|throwing|of)\s*(?:a\s*)?(?:number\s*)?([1-6])\b/.exec(q)) || (m = /\b([1-6])\b/.exec(q))){ fav = [+m[1]]; label = "a " + m[1]; }
    if(!fav || !fav.length) return null;
    return {text: steps("Let's find the probability for one fair die.", ["List all the possible outcomes.\n1, 2, 3, 4, 5, 6  (6 outcomes)", "List the favourable outcomes (" + label + ").\n" + fav.join(", ") + "  (" + fav.length + " outcome" + (fav.length > 1 ? "s" : "") + ")", "Probability = favourable ÷ total.\nP = " + fav.length + "/6 = " + probStr(fav.length, 6)], probStr(fav.length, 6)), topic: "probability"};
  }
  if(/\b(?:two|2|pair of)\s*(?:fair\s*)?(?:dice|die)\b/.test(q) && (m = /(?:sum|total)[^0-9]*(\d{1,2})/.exec(q))){
    const target = +m[1];
    if(target < 2 || target > 12) return null;
    let fav = 0; const combos = [];
    for(let a = 1; a <= 6; a++) for(let b = 1; b <= 6; b++) if(a + b === target){ fav++; combos.push("(" + a + "," + b + ")"); }
    return {text: steps("Let's find the probability for two fair dice.", ["There are 6 × 6 = 36 equally likely outcomes.", "List the outcomes that add to " + target + ".\n" + combos.join(" ") + "  (" + fav + " outcomes)", "Probability = favourable ÷ total.\nP = " + fav + "/36 = " + probStr(fav, 36)], probStr(fav, 36)), topic: "probability"};
  }
  if(/\bcoins?\b|\btoss|\bflip/.test(q)){
    const words = {one: 1, a: 1, two: 2, three: 3, four: 4, five: 5};
    const nm = /\b(one|two|three|four|five|\d)\s*(?:fair\s*)?(?:coins?|times|tosses|flips)/.exec(q);
    const n = nm ? (words[nm[1]] || +nm[1]) : 1;
    if(n < 1 || n > 10) return null;
    const total = Math.pow(2, n);
    const nCr = (a, b) => { let r = 1; for(let i = 1; i <= b; i++) r = r * (a - b + i) / i; return Math.round(r); };
    const head = /head/.test(q) ? "heads" : /tail/.test(q) ? "tails" : null;
    if(!head) return null;
    let fav, label;
    if((m = /at\s*least\s*one/.exec(q))){ fav = total - 1; label = "at least one " + head.slice(0, -1); }
    else if((m = /(?:exactly\s*)?(one|two|three|four|five|all|\d)\s*(?:heads|tails)/.exec(q))){
      const k = m[1] === "all" ? n : (words[m[1]] || +m[1]);
      if(k > n) return null;
      fav = nCr(n, k); label = "exactly " + k + " " + head;
    } else if(n === 1){ fav = 1; label = "one " + head.slice(0, -1); }
    else return null;
    const st = ["With " + n + " coin" + (n > 1 ? "s" : "") + " there are 2" + (n > 1 ? sup(n) : "") + " = " + total + " equally likely outcomes.", "Count the favourable outcomes (" + label + "): " + fav + (n > 1 ? "  (using " + n + "C" + (fav === total - 1 ? "…" : "k") + " counting)" : ""), "Probability = favourable ÷ total.\nP = " + fav + "/" + total + " = " + probStr(fav, total)];
    if(n > 1) st[1] = "Count the favourable outcomes (" + label + "): " + fav;
    return {text: steps("Let's find the probability for coin tosses.", st, probStr(fav, total)), topic: "probability"};
  }
  const colours = "red|blue|green|yellow|white|black|orange|pink|purple|brown|grey|gray";
  const reGlobal = new RegExp("(\\d+)\\s*(" + colours + ")", "g");
  const found = []; let cm;
  while((cm = reGlobal.exec(q))) found.push([cm[2], parseInt(cm[1], 10)]);
  if(found.length >= 2){
    const total = found.reduce((a, b) => a + b[1], 0);
    const tm = new RegExp("(?:of|get(?:ting)?|pick(?:ing)?|draw(?:ing)?|choos(?:e|ing)|select(?:ing)?|take|taking)\\s*(?:a\\s*|an\\s*|one\\s*)?(not\\s*)?(?:a\\s*|an\\s*)?(" + colours + ")\\b(?!\\s*\\d)").exec(q.replace(new RegExp("\\d+\\s*(" + colours + ")", "g"), "#"));
    if(tm){
      const entry = found.find(f => f[0] === tm[2]);
      if(!entry) return null;
      const fav = tm[1] ? total - entry[1] : entry[1];
      return {text: steps("Let's find the probability.", ["Find the total number of items.\n" + found.map(f => f[1]).join(" + ") + " = " + total, "Count the favourable ones (" + (tm[1] ? "not " : "") + tm[2] + "): " + fav, "Probability = favourable ÷ total.\nP = " + fav + "/" + total + " = " + probStr(fav, total)], probStr(fav, total)), topic: "probability"};
    }
  }
  if(/pack of cards|deck of cards|playing card|standard deck/.test(q)){
    let fav = null, label = "";
    if(/\bace\b/.test(q)){ fav = 4; label = "an ace"; }
    else if(/\bking\b/.test(q)){ fav = 4; label = "a king"; }
    else if(/\bqueen\b/.test(q)){ fav = 4; label = "a queen"; }
    else if(/face card|picture card/.test(q)){ fav = 12; label = "a face card (J, Q, K)"; }
    else if(/\bheart/.test(q) || /\bdiamond/.test(q) || /\bspade/.test(q) || /\bclub/.test(q)){ fav = 13; label = "that suit"; }
    else if(/\bred\b/.test(q) || /\bblack\b/.test(q)){ fav = 26; label = "that colour"; }
    if(!fav) return null;
    return {text: steps("Let's find the probability using a standard pack of 52 cards.", ["There are 52 cards in total.", "Count the favourable cards (" + label + "): " + fav, "Probability = favourable ÷ total.\nP = " + fav + "/52 = " + probStr(fav, 52)], probStr(fav, 52)), topic: "probability"};
  }
  return null;
}

/* ══════════════ GEOMETRY ══════════════ */
function geom(q){
  const num = re => { const m = re.exec(q); return m ? parseFloat(m[1]) : null; };
  const r = num(/radius\s*(?:of|is|=|:)?\s*(\d+(?:\.\d+)?)/) ?? (num(/diameter\s*(?:of|is|=|:)?\s*(\d+(?:\.\d+)?)/) != null ? num(/diameter\s*(?:of|is|=|:)?\s*(\d+(?:\.\d+)?)/) / 2 : null);
  const h = num(/(?:height|high|tall)\s*(?:of|is|=|:)?\s*(\d+(?:\.\d+)?)/);
  const base = num(/base\s*(?:of|is|=|:)?\s*(\d+(?:\.\d+)?)/);
  const pi = Math.PI;
  const u = (/\b(cm|mm|km|m|inches|inch|feet|ft)\b/.exec(q) || [])[1] || "";
  const sq = u ? u + "²" : "square units", cu = u ? u + "³" : "cubic units";
  if(/triangle/.test(q) && /area/.test(q) && base != null && h != null && !/hypotenuse/.test(q)){
    return {text: steps("Let's find the area of the triangle.", ["Write the formula: area = ½ × base × height.", "Substitute.\nArea = ½ × " + base + " × " + h + " = " + fnum(base * h / 2, 4) + " " + sq], fnum(base * h / 2, 4) + " " + sq), topic: "area_volume"};
  }
  if(/trapezi/.test(q) && /area/.test(q)){
    const pm = /(?:parallel\s*sides?|sides?)\s*(?:of|are|=|:)?\s*(\d+(?:\.\d+)?)\s*(?:and|,|&)\s*(\d+(?:\.\d+)?)/.exec(q);
    if(pm && h != null){
      const a = +pm[1], b = +pm[2];
      return {text: steps("Let's find the area of the trapezium.", ["Write the formula: area = ½ × (a + b) × height.", "Substitute.\nArea = ½ × (" + a + " + " + b + ") × " + h + " = " + fnum((a + b) * h / 2, 4) + " " + sq], fnum((a + b) * h / 2, 4) + " " + sq), topic: "area_volume"};
    }
  }
  if(/cylinder/.test(q) && /volume/.test(q) && r != null && h != null){
    const v = pi * r * r * h;
    return {text: steps("Let's find the volume of the cylinder.", ["Write the formula: V = πr²h.", "Substitute.\nV = π × " + r + "² × " + h + " = π × " + fnum(r * r * h, 4), "Calculate.\nV ≈ " + fnum(v, 2) + " " + cu], "V = " + fnum(r * r * h, 4) + "π ≈ " + fnum(v, 2) + " " + cu), topic: "area_volume"};
  }
  if(/cone/.test(q) && /volume/.test(q) && r != null && h != null){
    const v = pi * r * r * h / 3;
    return {text: steps("Let's find the volume of the cone.", ["Write the formula: V = ⅓πr²h.", "Substitute.\nV = ⅓ × π × " + r + "² × " + h, "Calculate.\nV ≈ " + fnum(v, 2) + " " + cu], "V ≈ " + fnum(v, 2) + " " + cu), topic: "area_volume"};
  }
  if(/sphere/.test(q) && r != null && /volume/.test(q)){
    const v = 4 / 3 * pi * Math.pow(r, 3);
    return {text: steps("Let's find the volume of the sphere.", ["Write the formula: V = 4/3 πr³.", "Substitute.\nV = 4/3 × π × " + r + "³ = 4/3 × π × " + fnum(Math.pow(r, 3), 4), "Calculate.\nV ≈ " + fnum(v, 2) + " " + cu], "V ≈ " + fnum(v, 2) + " " + cu), topic: "area_volume"};
  }
  if(/sphere/.test(q) && r != null && /surface/.test(q)){
    const a = 4 * pi * r * r;
    return {text: steps("Let's find the surface area of the sphere.", ["Write the formula: A = 4πr².", "Substitute.\nA = 4 × π × " + r + "² = " + fnum(4 * r * r, 4) + "π", "Calculate.\nA ≈ " + fnum(a, 2) + " " + sq], "A ≈ " + fnum(a, 2) + " " + sq), topic: "area_volume"};
  }
  if(/circle/.test(q) && /circumference/.test(q) && r != null){
    const c = 2 * pi * r;
    return {text: steps("Let's find the circumference of the circle.", ["Write the formula: C = 2πr.", "Substitute.\nC = 2 × π × " + r + " = " + fnum(2 * r, 4) + "π", "Calculate.\nC ≈ " + fnum(c, 2) + (u ? " " + u : "")], "C ≈ " + fnum(c, 2) + (u ? " " + u : "")), topic: "geometry"};
  }
  if(/cuboid|box|rectangular prism/.test(q) && /volume/.test(q)){
    let m = /(\d+(?:\.\d+)?)\s*(?:by|x|×|\*)\s*(\d+(?:\.\d+)?)\s*(?:by|x|×|\*)\s*(\d+(?:\.\d+)?)/.exec(q);
    let l, w, hh;
    if(m){ l = +m[1]; w = +m[2]; hh = +m[3]; }
    else { l = num(/length\s*(?:of|is|=|:)?\s*(\d+(?:\.\d+)?)/); w = num(/(?:width|breadth)\s*(?:of|is|=|:)?\s*(\d+(?:\.\d+)?)/); hh = h; }
    if(l != null && w != null && hh != null) return {text: steps("Let's find the volume of the cuboid.", ["Write the formula: V = length × width × height.", "Substitute.\nV = " + l + " × " + w + " × " + hh + " = " + fnum(l * w * hh, 4) + " " + cu], fnum(l * w * hh, 4) + " " + cu), topic: "area_volume"};
  }
  if(/cube/.test(q) && /volume/.test(q)){
    const s = num(/(?:side|edge|length)\s*(?:of|is|=|:)?\s*(\d+(?:\.\d+)?)/);
    if(s != null) return {text: steps("Let's find the volume of the cube.", ["Write the formula: V = side³.", "Substitute.\nV = " + s + "³ = " + fnum(Math.pow(s, 3), 4) + " " + cu], fnum(Math.pow(s, 3), 4) + " " + cu), topic: "area_volume"};
  }
  if(/hypotenuse|pythagor|right[\s-]*angled/.test(q)){
    const nums = (q.match(/\d+(?:\.\d+)?/g) || []).map(Number);
    if(nums.length === 2){
      if(/find\s*(?:the\s*)?(?:length of the\s*)?hypotenuse|longest side|hypotenuse\s*\?|what is the hypotenuse/.test(q) || !/hypotenuse\s*(?:is|=|of|:)\s*\d/.test(q)){
        const [a, b] = nums, c2 = a * a + b * b, c = Math.sqrt(c2);
        const sqn = perfectSquare(c2);
        return {text: steps("Let's use Pythagoras' theorem to find the hypotenuse.", ["Write the theorem: a² + b² = c², where c is the hypotenuse.", "Substitute.\n" + a + "² + " + b + "² = " + (a * a) + " + " + (b * b) + " = " + c2, "Take the square root.\nc = √" + c2 + " = " + (sqn >= 0 ? sqn : fnum(c, 4))], "hypotenuse = " + (sqn >= 0 ? sqn : fnum(c, 4))), topic: "geometry"};
      }
      const hm = /hypotenuse\s*(?:is|=|of|:)\s*(\d+(?:\.\d+)?)/.exec(q);
      if(hm){
        const c = +hm[1], a = nums.find(x => x !== c) ?? nums[0];
        if(a >= c) return null;
        const b2 = c * c - a * a, b = Math.sqrt(b2), sqn = perfectSquare(b2);
        return {text: steps("Let's use Pythagoras' theorem to find the missing side.", ["Write the theorem: a² + b² = c². Rearrange: b² = c² − a².", "Substitute.\nb² = " + c + "² − " + a + "² = " + (c * c) + " − " + (a * a) + " = " + b2, "Take the square root.\nb = √" + b2 + " = " + (sqn >= 0 ? sqn : fnum(b, 4))], "missing side = " + (sqn >= 0 ? sqn : fnum(b, 4))), topic: "geometry"};
      }
    }
  }
  return null;
}
function trigValues(q){
  const m = /\b(sin|cos|tan)\s*(?:\(\s*)?(?:of\s*)?(-?\d+(?:\.\d+)?)\s*(?:°|deg(?:rees?)?)?\s*\)?\s*$/.exec(q.replace(/[?.]+$/, "").trim());
  if(!m) return null;
  const f = m[1], ang = parseFloat(m[2]);
  const rad = ang * Math.PI / 180;
  const exact = {
    sin: {0: "0", 30: "1/2", 45: "√2/2", 60: "√3/2", 90: "1", 120: "√3/2", 135: "√2/2", 150: "1/2", 180: "0"},
    cos: {0: "1", 30: "√3/2", 45: "√2/2", 60: "1/2", 90: "0", 120: "-1/2", 135: "-√2/2", 150: "-√3/2", 180: "-1"},
    tan: {0: "0", 30: "√3/3 (= 1/√3)", 45: "1", 60: "√3", 135: "-1", 180: "0"}
  };
  let val = Math[f](rad);
  if(f === "tan" && Math.abs(Math.cos(rad)) < 1e-12) return {text: steps("Let's find tan " + ang + "°.", ["tan = sin ÷ cos, and cos " + ang + "° = 0, so tan is undefined here."], "undefined"), topic: "trigonometry"};
  if(Math.abs(val) < 1e-12) val = 0;
  const ex = exact[f][ang];
  const st = ["Use your calculator in DEGREE mode (or the special-angle values).\n" + f + " " + ang + "° ≈ " + fnum(val, 4)];
  if(ex) st.push("Exact value for this special angle: " + ex);
  return {text: steps("Let's find " + f + " " + ang + "°.", st, ex ? ex + " ≈ " + fnum(val, 4) : "≈ " + fnum(val, 4)), topic: "trigonometry"};
}
function standardForm(q){
  const m = /(\d[\d,]*(?:\.\d+)?|\.\d+)\s*(?:in|as|to|into)\s*(?:standard form|scientific notation)/.exec(q);
  if(!m) return null;
  const raw = m[1].replace(/,/g, ""), v = parseFloat(raw);
  if(!(v > 0)) return null;
  const exp = Math.floor(Math.log10(v) + 1e-12);
  const mant = v / Math.pow(10, exp);
  const mantStr = fnum(mant, 6);
  const moved = Math.abs(exp);
  return {text: steps("Let's write " + raw + " in standard form.", ["Standard form is a × 10ⁿ with 1 ≤ a < 10.", "Move the decimal point " + moved + " place" + (moved === 1 ? "" : "s") + " " + (exp >= 0 ? "to the left" : "to the right") + " so there is one non-zero digit before it: a = " + mantStr, "The power of 10 is " + (exp >= 0 ? "positive (" + exp + ")" : "negative (" + exp + ")") + " because the number is " + (exp >= 0 ? "large (10 or more)." : "small (less than 1).")], mantStr + " × 10" + sup(exp < 0 ? "-" + (-exp) : exp).replace("-", "⁻")), topic: "standard_form"};
}
function sequences(q){
  if(!/nth term|th term|(?:1st|2nd|3rd|\d+th) term|next term|sequence/.test(q)) return null;
  const listPart = q.replace(/\b\d+(?:st|nd|rd|th)\b/g, " ");
  const nums = (listPart.match(/-?\d+(?:\.\d+)?/g) || []).map(Number);
  if(nums.length < 3) return null;
  const arith = nums.every((v, i) => i === 0 || Math.abs((v - nums[i - 1]) - (nums[1] - nums[0])) < 1e-9);
  const ask = /(\d+)\s*(?:st|nd|rd|th)\s*term/.exec(q);
  if(arith){
    const a = nums[0], d = nums[1] - nums[0];
    const st = ["Find the common difference.\n" + nums[1] + " - " + nums[0] + " = " + fnum(d) + "  (the same each time, so it is an arithmetic sequence)", "Use the formula: nth term = a + (n − 1)d, with a = " + a + " and d = " + fnum(d) + ".", "Simplify.\nnth term = " + a + " + (n − 1)(" + fnum(d) + ") = " + (d === 0 ? a : (d === 1 ? "" : d === -1 ? "-" : fnum(d)) + "n" + (a - d === 0 ? "" : (a - d > 0 ? " + " : " - ") + Math.abs(a - d)))];
    let ans = "nth term = " + (d === 0 ? a : (d === 1 ? "" : d === -1 ? "-" : fnum(d)) + "n" + (a - d === 0 ? "" : (a - d > 0 ? " + " : " - ") + Math.abs(a - d)));
    if(ask){
      const k = parseInt(ask[1], 10), val = a + (k - 1) * d;
      st.push("The " + ask[1] + "th term: put n = " + k + ".\n" + a + " + (" + k + " − 1)(" + fnum(d) + ") = " + fnum(val));
      ans += ";  term " + k + " = " + fnum(val);
    } else if(/next/.test(q)) {
      const nxt = nums[nums.length - 1] + d;
      st.push("Next term = last term + d = " + nums[nums.length - 1] + " + " + fnum(d) + " = " + fnum(nxt));
      ans += ";  next term = " + fnum(nxt);
    }
    return {text: steps("Let's analyse the sequence " + nums.join(", ") + ".", st, ans), topic: "sequences"};
  }
  if(nums[0] !== 0 && nums.every((v, i) => i === 0 || (nums[i - 1] !== 0 && Math.abs(v / nums[i - 1] - nums[1] / nums[0]) < 1e-9))){
    const a = nums[0], r = nums[1] / nums[0];
    const st = ["Find the common ratio.\n" + nums[1] + " ÷ " + nums[0] + " = " + fnum(r) + "  (the same each time, so it is a geometric sequence)", "Use the formula: nth term = a × rⁿ⁻¹, with a = " + a + " and r = " + fnum(r) + ".\nnth term = " + a + " × " + fnum(r) + "ⁿ⁻¹"];
    let ans = "nth term = " + a + " × " + fnum(r) + "ⁿ⁻¹";
    if(ask){
      const k = parseInt(ask[1], 10);
      if(k > 40) return null;
      const val = a * Math.pow(r, k - 1);
      st.push("The " + ask[1] + "th term: n = " + k + ".\n" + a + " × " + fnum(r) + sup(k - 1) + " = " + fnum(val, 4));
      ans += ";  term " + k + " = " + fnum(val, 4);
    } else if(/next/.test(q)){
      const nxt = nums[nums.length - 1] * r;
      st.push("Next term = last term × r = " + nums[nums.length - 1] + " × " + fnum(r) + " = " + fnum(nxt, 4));
      ans += ";  next term = " + fnum(nxt, 4);
    }
    return {text: steps("Let's analyse the sequence " + nums.join(", ") + ".", st, ans), topic: "sequences"};
  }
  return null;
}

/* ══════════════ MAIN ENTRY ══════════════ */
const POLITE = /^(?:please\s+|pls\s+|can you\s+|could you\s+|help me\s+|i want to\s+|i need to\s+|how do i\s+|how to\s+|show me how to\s+|teach me how to\s+)+/;
function stripCommand(q, words){
  return q.replace(new RegExp("^(?:" + words + ")\\s*(?:the\\s+)?(?:equation\\s+|expression\\s+|polynomial\\s+|quadratic\\s+|function\\s+|brackets?\\s+)?(?:for\\s+x\\s*[:\\-]?\\s*)?", "i"), "");
}
function trimTail(s){
  return s.replace(/\s*(?:for|with respect to|wrt)\s*x\s*[?.!]*$/i, "").replace(/[?.!]+$/g, "").trim();
}
function pRight(s){ return s.replace(/^(?:y|f\(x\)|f\s*x|dy\/dx)\s*=\s*/i, ""); }

function baintSolve(question){
  try{
    let q = String(question || "").toLowerCase().replace(/[\u2212\u2013\u2014]/g, "-").replace(/[“”"]/g, "").trim();
    if(!q || q.length > 220) return null;
    q = q.replace(POLITE, "").replace(/\s+/g, " ").trim();
    let r;

    // word problems and special tasks first (they contain words, so they cannot be confused with algebra)
    if((r = interest(q))) return r;
    if((r = speedTasks(q))) return r;
    if((r = probabilityTasks(q))) return r;
    if((r = ratioShare(q))) return r;
    if((r = percentTasks(q))) return r;
    if((r = statsTasks(q))) return r;
    if((r = sequences(q))) return r;
    if((r = standardForm(q))) return r;
    if((r = geom(q))) return r;
    if((r = fractionTasks(q))) return r;
    if((r = roots(q))) return r;
    if((r = factorial(q))) return r;
    if((r = logarithm(q))) return r;
    if((r = trigValues(q))) return r;

    // simultaneous equations
    if(/=/.test(q) && /y/.test(q) && /x/.test(q) && (r = solveSimultaneous(q))) return r;

    // calculus
    let m = /^(?:differentiate|derivative of|find the derivative of|find dy\/dx(?: for| of)?|d\/dx(?: of)?|dy\/dx(?: of| for)?|find the gradient function of|differentiation of)\s*(.+)$/.exec(q);
    if(m){
      const body = trimTail(pRight(m[1]));
      const key = body.replace(/\(|\)/g, " ").replace(/\s+/g, " ").trim();
      if(STD_DERIV[key]) return {text: steps("Let's differentiate " + body + ".", [STD_DERIV[key][1]], STD_DERIV[key][0]), topic: "derivatives"};
      const p = parsePoly(body);
      if(p && pDeg(p) >= 0 && /x/.test(body) && pDeg(p) <= 8) return differentiate(p);
      return null;
    }
    m = /^(?:integrate|integral of|find the integral of|find the integration of|integration of|∫)\s*(.+)$/.exec(q);
    if(m){
      let body = trimTail(m[1]).replace(/\s*dx\s*$/, "");
      const lim = /^(.*?)\s*(?:from|between)\s*(-?[\d./]+)\s*(?:to|and)\s*(-?[\d./]+)\s*$/.exec(body);
      const key = body.replace(/\(|\)/g, " ").replace(/\s+/g, " ").trim();
      if(!lim && STD_INTEG[key]) return {text: steps("Let's integrate " + body + ".", [STD_INTEG[key][1]], STD_INTEG[key][0]), topic: "integrals"};
      if(lim){
        const p = parsePoly(lim[1].replace(/\s*dx\s*$/, "")), lo = parsePoly(lim[2]), hi = parsePoly(lim[3]);
        if(p && lo && hi && lo.length === 1 && hi.length === 1 && /x/.test(lim[1]) && pDeg(p) <= 8) return integrate(p, lo[0], hi[0]);
        return null;
      }
      const p = parsePoly(body);
      if(p && /x/.test(body) && pDeg(p) <= 8) return integrate(p);
      return null;
    }

    // factorise / expand
    m = /^(?:factori[sz]e|factori[sz]ing|factorization of|factorisation of|factori[sz]e fully)\s*(.+)$/.exec(q);
    if(m){
      const body = trimTail(stripCommand(m[1], "the expression|the quadratic|the equation|expression|quadratic"));
      const p = parsePoly(body);
      if(p && /x/.test(body)) return factorise(p);
      return null;
    }
    m = /^(?:expand|multiply out|expand and simplify|expand and collect)\s*(.+)$/.exec(q);
    if(m){
      const body = trimTail(stripCommand(m[1], "the brackets|the expression|brackets|expression"));
      if(/\(/.test(body) && /x/.test(body)) return expandText(body);
      return null;
    }

    // inequalities
    m = /^(?:solve\s*)?(?:the\s+)?(?:inequality\s*)?(.+?)\s*(<=|>=|≤|≥|<|>)\s*(.+)$/.exec(q.replace(/≤/g, "<=").replace(/≥/g, ">="));
    if(m && /x/.test(m[1] + m[3]) && !/[a-wyz]/.test(m[1].replace(/inequality|solve|the|for/g, "") + m[3])){
      const op = m[2].replace("≤", "<=").replace("≥", ">=");
      const pl = parsePoly(trimTail(m[1])), pr = parsePoly(trimTail(m[3]));
      if(pl && pr && pDeg(pl) <= 1 && pDeg(pr) <= 1) return solveInequality(pl, op, pr, trimTail(m[1]) + " " + op + " " + trimTail(m[3]));
    }

    // equations in x
    m = /^(?:solve|find x(?: in| if| when)?|find the roots of|find the solutions? (?:of|to)|what is x(?: in| if| when)?|find the value of x(?: in| if| when)?|solve for x(?:\s*[:\-])?|work out x(?: in| if| when)?)?\s*(.+)$/.exec(q);
    if(m){
      let body = trimTail(stripCommand(m[1], "the equation|equation|quadratic|the quadratic"));
      if((body.match(/=/g) || []).length === 1 && /x/.test(body) && !/[a-wyz]/.test(body.replace(/\bx\b/g, "x").replace(/[0-9x+\-*\/^().= ×÷²³]/g, ""))){
        const [L, R] = body.split("=");
        const pl = parsePoly(L), pr = parsePoly(R);
        if(pl && pr){
          const diff = pAdd(pl, pScale(pr, F(-1)));
          const deg = pDeg(diff);
          if(deg === 2) return solveQuadratic(diff);
          if(deg === 1 && (pDeg(pl) > 1 || pDeg(pr) > 1 || /\(|\//.test(body))) return solveLinear(pl, pr, body.trim());
        }
      }
    }
    return null;
  }catch(e){
    return null;
  }
}

window.baintSolve = baintSolve;
})();
