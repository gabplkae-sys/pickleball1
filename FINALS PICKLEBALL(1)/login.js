/* ============================================================
   Finals 2026 Pickleball - login.js

   This page only signs people in. After a correct login it opens
   index.html. Accounts are created inside index.html (Settings).

   DEFAULT_ACCOUNTS is used ONLY the very first time, when no
   accounts exist yet, so you have an Admin to sign in with.
   Change the Admin password after your first login.

   NOTE: this all runs in the browser, so it is a good school
   project login, but it is NOT real security. A real system
   checks passwords on a server.
   ============================================================ */

const DEFAULT_ACCOUNTS = [
    { username:"admin", password:"admin123", role:"Admin" },
    { username:"staff", password:"staff123", role:"Staff" }
];

// These keys are shared with script.js, so keep them identical in both files.
const USERS_KEY = "pickleball_users";
const SESSION_KEY = "pickleball_session";
const LOGOUT_MSG_KEY = "pickleball_logout_msg";
const LOCK_KEY = "pickleball_lock";

const MAX_ATTEMPTS = 5;           // wrong passwords allowed in a row
const LOCK_MS = 30 * 1000;        // lockout length (30 seconds)
const NEXT_PAGE = "index.html";   // where to go after login

/* ---------- PASSWORD HASHING ---------- */

// SHA-256 (works even when the page is opened as a plain file)
function sha256(str) {
    const rrot = (v, a) => (v >>> a) | (v << (32 - a));
    const bytes = unescape(encodeURIComponent(str)).split("").map(ch => ch.charCodeAt(0));
    const bitLen = bytes.length * 8;

    bytes.push(0x80);
    while (bytes.length % 64 !== 56) bytes.push(0);
    [Math.floor(bitLen / 4294967296), bitLen >>> 0].forEach(word => {
        for (let s = 24; s >= 0; s -= 8) bytes.push((word >>> s) & 255);
    });

    const K = [];
    const H = [];
    let n = 0;
    for (let p = 2; n < 64; p++) {
        let prime = true;
        for (let d = 2; d * d <= p; d++) {
            if (p % d === 0) { prime = false; break; }
        }
        if (!prime) continue;
        if (n < 8) H[n] = (Math.sqrt(p) % 1 * 4294967296) | 0;
        K[n] = (Math.cbrt(p) % 1 * 4294967296) | 0;
        n++;
    }

    for (let i = 0; i < bytes.length; i += 64) {
        const w = [];
        for (let j = 0; j < 64; j++) {
            if (j < 16) {
                w[j] = (bytes[i + j*4] << 24) | (bytes[i + j*4 + 1] << 16) | (bytes[i + j*4 + 2] << 8) | bytes[i + j*4 + 3];
            } else {
                const s0 = rrot(w[j-15], 7) ^ rrot(w[j-15], 18) ^ (w[j-15] >>> 3);
                const s1 = rrot(w[j-2], 17) ^ rrot(w[j-2], 19) ^ (w[j-2] >>> 10);
                w[j] = (w[j-16] + s0 + w[j-7] + s1) | 0;
            }
        }

        let [a, b, c, d, e, f, g, h] = H;
        for (let j = 0; j < 64; j++) {
            const S1 = rrot(e, 6) ^ rrot(e, 11) ^ rrot(e, 25);
            const ch = (e & f) ^ (~e & g);
            const t1 = (h + S1 + ch + K[j] + w[j]) | 0;
            const S0 = rrot(a, 2) ^ rrot(a, 13) ^ rrot(a, 22);
            const maj = (a & b) ^ (a & c) ^ (b & c);
            const t2 = (S0 + maj) | 0;
            h = g; g = f; f = e; e = (d + t1) | 0;
            d = c; c = b; b = a; a = (t1 + t2) | 0;
        }

        [a, b, c, d, e, f, g, h].forEach((v, k) => { H[k] = (H[k] + v) | 0; });
    }

    return H.map(v => (v >>> 0).toString(16).padStart(8, "0")).join("");
}

// salted and repeated, so the same password never looks the same twice
function hashPassword(password, salt) {
    let h = sha256(salt + ":" + password);
    for (let i = 0; i < 999; i++) h = sha256(h + salt);
    return h;
}

function uid() {
    return Date.now().toString(36) + Math.random().toString(36).slice(2, 7);
}

/* ---------- ACCOUNTS ---------- */

function loadUsers() {
    try {
        const saved = JSON.parse(localStorage.getItem(USERS_KEY));
        if (saved && Array.isArray(saved.users) && saved.users.length) return saved.users;
    } catch (e) {}

    // first run: create the default accounts (passwords are stored hashed)
    const created = DEFAULT_ACCOUNTS.map(a => {
        const salt = uid() + uid();
        return {
            id: uid(),
            username: a.username,
            role: a.role,
            salt,
            hash: hashPassword(a.password, salt),
            memberId: null
        };
    });

    try {
        localStorage.setItem(USERS_KEY, JSON.stringify({ version:1, users:created }));
    } catch (e) {}

    return created;
}

const users = loadUsers();

/* ---------- PAGE HELPERS ---------- */

function setMsg(text, type) {
    const el = document.getElementById("loginMsg");

    if (!text) {
        el.classList.add("hidden");
        return;
    }

    el.textContent = text;
    el.className = "login-msg " + type;
}

function togglePw() {
    const input = document.getElementById("loginPass");
    const button = document.querySelector(".pw-toggle");
    const show = input.type === "password";

    input.type = show ? "text" : "password";
    button.textContent = show ? "Hide" : "Show";
}

function getLock() {
    try {
        return JSON.parse(localStorage.getItem(LOCK_KEY)) || { count:0, until:0 };
    } catch (e) {
        return { count:0, until:0 };
    }
}

function setLock(lock) {
    try { localStorage.setItem(LOCK_KEY, JSON.stringify(lock)); } catch (e) {}
}

/* ---------- LOGIN ---------- */

function doLogin(e) {
    e.preventDefault();

    const username = document.getElementById("loginUser").value.trim();
    const password = document.getElementById("loginPass").value;
    const lock = getLock();
    const now = Date.now();

    if (lock.until > now) {
        const secs = Math.ceil((lock.until - now) / 1000);
        setMsg("Too many failed attempts. Try again in " + secs + " seconds.", "err");
        return;
    }

    if (!username || !password) {
        setMsg("Enter your username and password.", "err");
        return;
    }

    const user = users.find(u => u.username.toLowerCase() === username.toLowerCase());

    if (!user || user.hash !== hashPassword(password, user.salt)) {
        lock.count++;
        if (lock.count >= MAX_ATTEMPTS) {
            lock.count = 0;
            lock.until = now + LOCK_MS;
        }
        setLock(lock);

        setMsg("Incorrect username or password.", "err");
        document.getElementById("loginPass").value = "";
        return;
    }

    setLock({ count:0, until:0 });

    try {
        sessionStorage.setItem(SESSION_KEY, JSON.stringify({
            username: user.username,
            at: new Date().toISOString()
        }));
    } catch (err) {
        setMsg("This browser is blocking storage, so login can't continue.", "err");
        return;
    }

    location.replace(NEXT_PAGE);
}

/* ---------- START ---------- */

(function init() {
    // already signed in? go straight to the system
    try {
        const saved = JSON.parse(sessionStorage.getItem(SESSION_KEY));
        if (saved && users.some(u => u.username === saved.username)) {
            location.replace(NEXT_PAGE);
            return;
        }
    } catch (e) {}

    // message left by the system (for example after logout)
    try {
        const message = sessionStorage.getItem(LOGOUT_MSG_KEY);
        if (message) {
            sessionStorage.removeItem(LOGOUT_MSG_KEY);
            setMsg(message, "ok");
        }
    } catch (e) {}

    document.getElementById("loginUser").focus();
})();