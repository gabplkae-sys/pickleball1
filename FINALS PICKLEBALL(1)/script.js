/* ============================================================
   Finals 2026 Pickleball - script.js
   Data is saved in the browser (localStorage). Role selection
   is a demo only, not secure login.
   ============================================================ */

const STORE_KEY = "pickleball_finals_2026";

const roles = {
    Admin: [
        ["📊","Dashboard","dashboard"],
        ["👥","Members","members"],
        ["📦","Inventory","inventory"],
        ["🚪","Attendance","attendance"],
        ["📢","Announcements","announcements"],
        ["🧾","Reports","reports"],
        ["⚙️","Settings","settings"]
    ],
    Staff: [
        ["📊","Dashboard","dashboard"],
        ["👥","Members","members"],
        ["📦","Inventory","inventory"],
        ["🚪","Attendance","attendance"],
        ["📢","Announcements","announcements"],
        ["🧾","Reports","reports"]
    ],
    Members: [
        ["📊","Dashboard","dashboard"],
        ["👤","My Profile","profile"],
        ["🚪","My Attendance","attendance"],
        ["📢","Announcements","announcements"]
    ]
};

const titles = {
    dashboard:"Dashboard",
    members:"Member Management",
    inventory:"Inventory Management",
    attendance:"Attendance Monitoring",
    announcements:"Announcements",
    reports:"Reports and Analytics",
    settings:"System Settings",
    profile:"My Profile"
};

// These keys are shared with login.js, so keep them identical in both files.
const USERS_KEY = "pickleball_users";
const SESSION_KEY = "pickleball_session";
const LOGOUT_MSG_KEY = "pickleball_logout_msg";

const IDLE_MS = 15 * 60 * 1000;   // auto logout after 15 minutes of no activity

let currentRole = "";
let currentUser = null;
let viewAsId = "";
let idleTimer = null;
let db = loadDB();
let users = loadUsers();

/* ---------- HELPERS ---------- */

function uid() {
    return Date.now().toString(36) + Math.random().toString(36).slice(2, 7);
}

function esc(value) {
    return String(value == null ? "" : value)
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#39;");
}

function toISODate(d) {
    return d.getFullYear() + "-" +
        String(d.getMonth() + 1).padStart(2, "0") + "-" +
        String(d.getDate()).padStart(2, "0");
}

function addDays(date, days) {
    const d = new Date(date);
    d.setDate(d.getDate() + days);
    return d;
}

function fmtDateTime(iso) {
    if (!iso) return "-";
    return new Date(iso).toLocaleString([], {
        month:"short", day:"numeric", hour:"2-digit", minute:"2-digit"
    });
}

function fmtDate(iso) {
    if (!iso) return "-";
    return new Date(iso + "T00:00:00").toLocaleDateString([], {
        year:"numeric", month:"short", day:"numeric"
    });
}

function daysLeft(member) {
    return Math.ceil((new Date(member.expiry + "T23:59:59") - new Date()) / 86400000);
}

function memberStatus(member) {
    const left = daysLeft(member);
    if (left < 0) return { label:"Expired", cls:"bad" };
    if (left <= 7) return { label:"Expiring", cls:"warn" };
    return { label:"Active", cls:"ok" };
}

function isStaffRole() {
    return currentRole === "Admin" || currentRole === "Staff";
}

function getMember(id) {
    return db.members.find(m => m.id === id);
}

/* ---------- PASSWORD HASHING ---------- */

// SHA-256 (works even when opened as a plain file)
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

function makeUser(username, password, role, memberId) {
    const salt = uid() + uid();
    return {
        id: uid(),
        username,
        salt,
        hash: hashPassword(password, salt),
        role,
        memberId: memberId || null
    };
}

// Accounts live in their own storage key so login.html and index.html share them.
function loadUsers() {
    try {
        const saved = JSON.parse(localStorage.getItem(USERS_KEY));
        if (saved && Array.isArray(saved.users)) return saved.users;
    } catch (e) {}
    return [];
}

function saveUsers() {
    try {
        localStorage.setItem(USERS_KEY, JSON.stringify({ version:1, users }));
    } catch (e) {}
}

function validateCredentials(username, password) {
    if (!/^[A-Za-z0-9._-]{3,20}$/.test(username)) {
        return "Username must be 3-20 characters (letters, numbers, . _ -).";
    }
    if (password.length < 6) return "Password must be at least 6 characters.";
    if (users.some(u => u.username.toLowerCase() === username.toLowerCase())) {
        return "That username is already taken.";
    }
    return "";
}

/* ---------- STORAGE ---------- */

function seedData() {
    const today = new Date();
    const data = {
        members: [
            { id:uid(), name:"Juan Dela Cruz", rfid:"1001", contact:"juan@email.com", type:"Monthly", expiry:toISODate(addDays(today, 20)) },
            { id:uid(), name:"Maria Santos", rfid:"1002", contact:"0917 000 0002", type:"Yearly", expiry:toISODate(addDays(today, 300)) },
            { id:uid(), name:"Pedro Reyes", rfid:"1003", contact:"0917 000 0003", type:"Monthly", expiry:toISODate(addDays(today, 4)) }
        ],
        inventory: [
            { id:uid(), name:"Paddle", category:"Equipment", total:20 },
            { id:uid(), name:"Pickleball", category:"Equipment", total:60 },
            { id:uid(), name:"Portable Net", category:"Court", total:4 }
        ],
        borrows: [],
        attendance: [],
        announcements: [
            { id:uid(), title:"Welcome to Finals 2026", body:"Please tap your RFID card when entering and leaving the courts.", date:new Date().toISOString() }
        ],
        activities: []
    };
    return data;
}

function loadDB() {
    try {
        const saved = localStorage.getItem(STORE_KEY);
        if (saved) return JSON.parse(saved);
    } catch (e) {}
    const fresh = seedData();
    try { localStorage.setItem(STORE_KEY, JSON.stringify(fresh)); } catch (e) {}
    return fresh;
}

function saveDB() {
    try { localStorage.setItem(STORE_KEY, JSON.stringify(db)); } catch (e) {}
}

function addActivity(icon, text) {
    db.activities.unshift({ icon, text, time:new Date().toISOString() });
    db.activities = db.activities.slice(0, 30);
}

function commit() {
    saveDB();
    renderAll();
}

/* ---------- LOGIN / NAVIGATION ---------- */

function startSession(user) {
    currentUser = user;
    currentRole = user.role;
    viewAsId = user.memberId || "";

    document.getElementById("app").classList.remove("hidden");

    document.getElementById("roleName").textContent = user.role.toUpperCase() + " WORKSPACE";
    document.getElementById("userBadge").textContent = "👤 " + user.username;
    document.getElementById("welcomeText").textContent =
        "Welcome back, " + user.username + ". This is your " + user.role + " dashboard.";

    // show or hide parts that depend on the role
    document.querySelectorAll("[data-roles]").forEach(el => {
        el.classList.toggle("hidden", !el.dataset.roles.split(",").includes(user.role));
    });

    buildNavigation();
    renderAll();
    showPage("dashboard");
    resetIdle();
}

/* ---------- AUTO LOGOUT (inactivity) ---------- */

function resetIdle() {
    if (!currentUser) return;
    clearTimeout(idleTimer);
    idleTimer = setTimeout(() => {
        logout("You were logged out after 15 minutes of inactivity.");
    }, IDLE_MS);
}

/* ---------- CHANGE MY PASSWORD ---------- */

function openPasswordModal() {
    ["cpOld","cpNew","cpConfirm"].forEach(id => document.getElementById(id).value = "");
    document.getElementById("pwModal").classList.remove("hidden");
    document.getElementById("cpOld").focus();
}

function closePasswordModal() {
    document.getElementById("pwModal").classList.add("hidden");
}

function submitPasswordChange(e) {
    e.preventDefault();

    const user = currentUser && users.find(u => u.id === currentUser.id);
    if (!user) return;

    const oldPw = document.getElementById("cpOld").value;
    const newPw = document.getElementById("cpNew").value;
    const confirmPw = document.getElementById("cpConfirm").value;

    if (user.hash !== hashPassword(oldPw, user.salt)) {
        showMessage("Current password is incorrect.");
        return;
    }
    if (newPw.length < 6) {
        showMessage("New password must be at least 6 characters.");
        return;
    }
    if (newPw !== confirmPw) {
        showMessage("New passwords do not match.");
        return;
    }
    if (newPw === oldPw) {
        showMessage("Choose a password different from the current one.");
        return;
    }

    user.salt = uid() + uid();
    user.hash = hashPassword(newPw, user.salt);
    saveUsers();
    closePasswordModal();
    showMessage("Password changed.");
}

/* ---------- USER ACCOUNTS (Admin creates accounts here) ---------- */

function toggleUserMember() {
    const isMember = document.getElementById("uRole").value === "Members";
    document.getElementById("uMember").classList.toggle("hidden", !isMember);
}

function addUser() {
    if (currentRole !== "Admin") return;

    const username = document.getElementById("uName").value.trim();
    const password = document.getElementById("uPass").value;
    const role = document.getElementById("uRole").value;
    let memberId = null;

    if (role === "Members") {
        memberId = document.getElementById("uMember").value;

        if (!memberId) {
            showMessage("Choose which member this account belongs to.");
            return;
        }
    }

    const problem = validateCredentials(username, password);
    if (problem) {
        showMessage(problem);
        return;
    }

    users.push(makeUser(username, password, role, memberId));
    saveUsers();
    addActivity("🔑", "Account created: " + username + " (" + role + ")");

    document.getElementById("uName").value = "";
    document.getElementById("uPass").value = "";
    commit();
    showMessage("Account created.");
}

function deleteUser(id) {
    if (currentRole !== "Admin") return;

    const user = users.find(u => u.id === id);
    if (!user) return;

    if (currentUser && user.id === currentUser.id) {
        showMessage("You can't delete the account you are signed in with.");
        return;
    }

    if (user.role === "Admin" && users.filter(u => u.role === "Admin").length <= 1) {
        showMessage("There must be at least one Admin account.");
        return;
    }

    if (!confirm("Delete the account '" + user.username + "'?")) return;

    users = users.filter(u => u.id !== id);
    saveUsers();
    addActivity("🗑️", "Account removed: " + user.username);
    commit();
}

/* ---------- RESET SOMEONE ELSE'S PASSWORD (Admin) ---------- */

let resetTargetId = "";

function openResetModal(id) {
    if (currentRole !== "Admin") return;

    const user = users.find(u => u.id === id);
    if (!user) return;

    resetTargetId = id;
    document.getElementById("resetTitle").textContent = "Reset password for " + user.username;
    document.getElementById("rpNew").value = "";
    document.getElementById("resetModal").classList.remove("hidden");
    document.getElementById("rpNew").focus();
}

function closeResetModal() {
    document.getElementById("resetModal").classList.add("hidden");
    resetTargetId = "";
}

function submitPasswordReset(e) {
    e.preventDefault();
    if (currentRole !== "Admin") return;

    const user = users.find(u => u.id === resetTargetId);
    const newPw = document.getElementById("rpNew").value;

    if (!user) return;

    if (newPw.length < 6) {
        showMessage("Password must be at least 6 characters.");
        return;
    }

    user.salt = uid() + uid();
    user.hash = hashPassword(newPw, user.salt);
    saveUsers();
    addActivity("🔑", "Password reset for " + user.username);
    closeResetModal();
    commit();
    showMessage("Password reset for " + user.username + ".");
}

/* ---------- ACCOUNT LIST ---------- */

function renderUserMemberPicker() {
    const select = document.getElementById("uMember");
    if (!select) return;

    const previous = select.value;
    const free = db.members.filter(m => !users.some(u => u.memberId === m.id));

    select.innerHTML = free.length
        ? '<option value="">Select member...</option>' +
          free.map(m => '<option value="' + m.id + '">' + esc(m.name) + " (RFID " + esc(m.rfid) + ")</option>").join("")
        : '<option value="">All members already have accounts</option>';

    if (free.some(m => m.id === previous)) select.value = previous;
}

function renderUsers() {
    const box = document.getElementById("userContent");
    if (!box) return;

    renderUserMemberPicker();

    const rows = users.map(u => {
        const member = u.memberId ? getMember(u.memberId) : null;
        const isMe = currentUser && u.id === currentUser.id;

        return "<tr>" +
            "<td>" + esc(u.username) + (isMe ? " (you)" : "") + "</td>" +
            "<td>" + esc(u.role) + "</td>" +
            "<td>" + esc(member ? member.name : "-") + "</td>" +
            "<td>" + (isMe ? "" :
                '<button class="mini-btn" onclick="openResetModal(\'' + u.id + '\')">Reset password</button>' +
                '<button class="mini-btn del" onclick="deleteUser(\'' + u.id + '\')">Delete</button>') + "</td>" +
            "</tr>";
    }).join("");

    box.innerHTML =
        "<table><thead><tr><th>Username</th><th>Role</th><th>Linked member</th><th></th></tr></thead><tbody>" +
        rows + "</tbody></table>";
}

function buildNavigation() {
    const nav = document.getElementById("navigation");
    nav.innerHTML = "";

    roles[currentRole].forEach(item => {
        const button = document.createElement("button");
        button.innerHTML = item[0] + " " + item[1];
        button.onclick = () => showPage(item[2]);
        button.dataset.page = item[2];
        nav.appendChild(button);
    });
}

function showPage(page) {
    const allowed = roles[currentRole].some(item => item[2] === page);

    if (!allowed) {
        showMessage("You don't have access to this page.");
        return;
    }

    document.querySelectorAll(".page").forEach(section => section.classList.remove("active"));
    document.getElementById(page).classList.add("active");

    document.querySelectorAll("nav button").forEach(button => {
        button.classList.toggle("active", button.dataset.page === page);
    });

    document.getElementById("pageTitle").textContent = titles[page];

    if (page === "attendance" && isStaffRole()) {
        setTimeout(() => document.getElementById("rfidInput").focus(), 50);
    }
}

function logout(message) {
    clearTimeout(idleTimer);
    currentRole = "";
    currentUser = null;
    viewAsId = "";

    try {
        sessionStorage.removeItem(SESSION_KEY);
        // login.html shows this message once, then forgets it
        sessionStorage.setItem(LOGOUT_MSG_KEY, typeof message === "string" ? message : "You have been logged out.");
    } catch (e) {}

    document.getElementById("app").classList.add("hidden");
    location.replace("login.html");
}

function toggleTheme() {
    const dark = document.documentElement.getAttribute("data-theme") === "dark";
    const next = dark ? "light" : "dark";
    document.documentElement.setAttribute("data-theme", next);
    try { localStorage.setItem("pickleball_theme", next); } catch (e) {}
}

function showMessage(message) {
    const toast = document.getElementById("toast");
    toast.textContent = message;
    toast.classList.remove("hidden");
    clearTimeout(showMessage.timer);
    showMessage.timer = setTimeout(() => toast.classList.add("hidden"), 2800);
}

/* ---------- MEMBERS ---------- */

function registerMember() {
    const name = document.getElementById("mName").value.trim();
    const rfid = document.getElementById("mRfid").value.trim();
    const contact = document.getElementById("mContact").value.trim();
    const type = document.getElementById("mType").value;
    let expiry = document.getElementById("mExpiry").value;

    if (!name || !rfid) {
        showMessage("Name and RFID number are required.");
        return;
    }

    if (db.members.some(m => m.rfid.toLowerCase() === rfid.toLowerCase())) {
        showMessage("That RFID number is already registered.");
        return;
    }

    if (!expiry) {
        const days = { "Day Pass":1, "Monthly":30, "Quarterly":90, "Yearly":365 }[type];
        expiry = toISODate(addDays(new Date(), days));
    }

    db.members.push({ id:uid(), name, rfid, contact, type, expiry });
    addActivity("👥", "New member registered: " + name);

    ["mName","mRfid","mContact","mExpiry"].forEach(id => document.getElementById(id).value = "");

    commit();
    showMessage("Member registered.");
}

function renewMember(id) {
    const member = getMember(id);
    if (!member) return;

    const start = new Date(member.expiry + "T00:00:00") > new Date()
        ? new Date(member.expiry + "T00:00:00")
        : new Date();

    member.expiry = toISODate(addDays(start, 30));
    addActivity("🔁", member.name + " membership renewed (+30 days)");
    commit();
    showMessage("Membership renewed for 30 days.");
}

function deleteMember(id) {
    const member = getMember(id);
    if (!member || !confirm("Delete " + member.name + "?")) return;

    db.members = db.members.filter(m => m.id !== id);
    users = users.filter(u => u.memberId !== id);   // remove the member's login too
    saveUsers();
    addActivity("🗑️", "Member removed: " + member.name);
    commit();
}

function renderMembers() {
    const q = document.getElementById("searchMembers").value.trim().toLowerCase();

    const list = db.members.filter(m =>
        !q || [m.name, m.rfid, m.contact].join(" ").toLowerCase().includes(q)
    );

    if (!list.length) {
        document.getElementById("memberContent").innerHTML = '<p class="empty">No members found.</p>';
        return;
    }

    const rows = list.map(m => {
        const s = memberStatus(m);
        let actions = "";
        if (isStaffRole()) actions += '<button class="mini-btn" onclick="renewMember(\'' + m.id + '\')">Renew +30d</button>';
        if (currentRole === "Admin") actions += '<button class="mini-btn del" onclick="deleteMember(\'' + m.id + '\')">Delete</button>';

        return "<tr>" +
            "<td>" + esc(m.name) + "</td>" +
            "<td>" + esc(m.rfid) + "</td>" +
            "<td>" + esc(m.contact || "-") + "</td>" +
            "<td>" + esc(m.type) + "</td>" +
            "<td>" + fmtDate(m.expiry) + "</td>" +
            '<td><span class="badge ' + s.cls + '">' + s.label + "</span></td>" +
            "<td>" + actions + "</td>" +
            "</tr>";
    }).join("");

    document.getElementById("memberContent").innerHTML =
        "<table><thead><tr><th>Name</th><th>RFID</th><th>Contact</th><th>Type</th><th>Expiry</th><th>Status</th><th></th></tr></thead><tbody>" +
        rows + "</tbody></table>";
}

/* ---------- INVENTORY ---------- */

function borrowedQty(itemId) {
    return db.borrows
        .filter(b => b.itemId === itemId && !b.returned)
        .reduce((sum, b) => sum + b.qty, 0);
}

function addItem() {
    const name = document.getElementById("iName").value.trim();
    const category = document.getElementById("iCategory").value.trim() || "General";
    const qty = parseInt(document.getElementById("iQty").value, 10);

    if (!name || !qty || qty < 1) {
        showMessage("Enter an item name and a quantity of at least 1.");
        return;
    }

    const existing = db.inventory.find(i => i.name.toLowerCase() === name.toLowerCase());

    if (existing) {
        existing.total += qty;
        addActivity("📦", "Stock added: " + qty + " x " + existing.name);
    } else {
        db.inventory.push({ id:uid(), name, category, total:qty });
        addActivity("📦", "New item added: " + name + " (" + qty + ")");
    }

    ["iName","iCategory","iQty"].forEach(id => document.getElementById(id).value = "");
    commit();
    showMessage("Inventory updated.");
}

function borrowItem(itemId) {
    const item = db.inventory.find(i => i.id === itemId);
    if (!item) return;

    const available = item.total - borrowedQty(itemId);
    if (available < 1) {
        showMessage("No available stock for " + item.name + ".");
        return;
    }

    const borrower = prompt("Borrower name (member or guest):");
    if (!borrower || !borrower.trim()) return;

    const qty = parseInt(prompt("Quantity to borrow (available: " + available + "):", "1"), 10);
    if (!qty || qty < 1 || qty > available) {
        showMessage("Invalid quantity.");
        return;
    }

    db.borrows.unshift({
        id:uid(), itemId, itemName:item.name,
        borrower:borrower.trim(), qty,
        date:new Date().toISOString(), returned:false, returnedDate:null
    });

    addActivity("📤", borrower.trim() + " borrowed " + qty + " x " + item.name);
    commit();
}

function returnItem(borrowId) {
    const record = db.borrows.find(b => b.id === borrowId);
    if (!record || record.returned) return;

    record.returned = true;
    record.returnedDate = new Date().toISOString();
    addActivity("📥", record.borrower + " returned " + record.qty + " x " + record.itemName);
    commit();
}

function deleteItem(itemId) {
    const item = db.inventory.find(i => i.id === itemId);
    if (!item) return;

    if (borrowedQty(itemId) > 0) {
        showMessage("Cannot delete: some units are still borrowed.");
        return;
    }

    if (!confirm("Delete " + item.name + " from inventory?")) return;

    db.inventory = db.inventory.filter(i => i.id !== itemId);
    addActivity("🗑️", "Item removed: " + item.name);
    commit();
}

function renderInventory() {
    if (!db.inventory.length) {
        document.getElementById("inventoryContent").innerHTML = '<p class="empty">No items yet.</p>';
    } else {
        const rows = db.inventory.map(i => {
            const out = borrowedQty(i.id);
            const left = i.total - out;
            let actions = "";
            if (isStaffRole()) actions += '<button class="mini-btn" onclick="borrowItem(\'' + i.id + '\')">Borrow</button>';
            if (currentRole === "Admin") actions += '<button class="mini-btn del" onclick="deleteItem(\'' + i.id + '\')">Delete</button>';

            return "<tr>" +
                "<td>" + esc(i.name) + "</td>" +
                "<td>" + esc(i.category) + "</td>" +
                "<td>" + i.total + "</td>" +
                "<td>" + out + "</td>" +
                '<td><span class="badge ' + (left === 0 ? "bad" : left <= 2 ? "warn" : "ok") + '">' + left + "</span></td>" +
                "<td>" + actions + "</td>" +
                "</tr>";
        }).join("");

        document.getElementById("inventoryContent").innerHTML =
            "<table><thead><tr><th>Item</th><th>Category</th><th>Total</th><th>Borrowed</th><th>Available</th><th></th></tr></thead><tbody>" +
            rows + "</tbody></table>";
    }

    if (!db.borrows.length) {
        document.getElementById("borrowContent").innerHTML = '<p class="empty">No borrow records yet.</p>';
        return;
    }

    const borrowRows = db.borrows.slice(0, 50).map(b =>
        "<tr>" +
        "<td>" + esc(b.itemName) + "</td>" +
        "<td>" + esc(b.borrower) + "</td>" +
        "<td>" + b.qty + "</td>" +
        "<td>" + fmtDateTime(b.date) + "</td>" +
        '<td><span class="badge ' + (b.returned ? "ok" : "warn") + '">' + (b.returned ? "Returned" : "Borrowed") + "</span></td>" +
        "<td>" + (!b.returned && isStaffRole() ? '<button class="mini-btn" onclick="returnItem(\'' + b.id + '\')">Mark Returned</button>' : "") + "</td>" +
        "</tr>"
    ).join("");

    document.getElementById("borrowContent").innerHTML =
        "<table><thead><tr><th>Item</th><th>Borrower</th><th>Qty</th><th>Date</th><th>Status</th><th></th></tr></thead><tbody>" +
        borrowRows + "</tbody></table>";
}

/* ---------- ATTENDANCE / RFID ---------- */

function scanRFID() {
    const input = document.getElementById("rfidInput");
    const tag = input.value.trim();
    input.value = "";
    input.focus();

    if (!tag) return;

    const member = db.members.find(m => m.rfid.toLowerCase() === tag.toLowerCase());

    if (!member) {
        showMessage("Unknown RFID: " + tag);
        return;
    }

    const open = db.attendance.find(a => a.memberId === member.id && !a.out);

    if (open) {
        open.out = new Date().toISOString();
        addActivity("🔴", member.name + " left the facility");
        commit();
        showMessage(member.name + " checked OUT.");
        return;
    }

    if (daysLeft(member) < 0) {
        showMessage(member.name + "'s membership is expired. Entry denied.");
        addActivity("⛔", "Entry denied (expired): " + member.name);
        commit();
        return;
    }

    db.attendance.unshift({
        id:uid(), memberId:member.id, name:member.name,
        in:new Date().toISOString(), out:null
    });

    addActivity("🟢", member.name + " entered the facility");
    commit();
    showMessage(member.name + " checked IN.");
}

function renderAttendance() {
    const isMember = currentRole === "Members";
    let records = db.attendance;

    document.getElementById("attendanceTitle").textContent =
        isMember ? "My Attendance" : "Attendance Records";

    if (isMember) {
        records = records.filter(a => a.memberId === viewAsId);
    }

    if (!records.length) {
        document.getElementById("attendanceContent").innerHTML = '<p class="empty">No attendance records yet.</p>';
        return;
    }

    const rows = records.slice(0, 100).map(a =>
        "<tr>" +
        "<td>" + esc(a.name) + "</td>" +
        "<td>" + fmtDateTime(a.in) + "</td>" +
        "<td>" + fmtDateTime(a.out) + "</td>" +
        '<td><span class="badge ' + (a.out ? "ok" : "warn") + '">' + (a.out ? "Left" : "Inside") + "</span></td>" +
        "</tr>"
    ).join("");

    document.getElementById("attendanceContent").innerHTML =
        "<table><thead><tr><th>Member</th><th>Entry</th><th>Exit</th><th>Status</th></tr></thead><tbody>" +
        rows + "</tbody></table>";
}

/* ---------- ANNOUNCEMENTS ---------- */

function postAnnouncement() {
    const title = document.getElementById("aTitle").value.trim();
    const body = document.getElementById("aBody").value.trim();

    if (!title || !body) {
        showMessage("Enter both a title and a message.");
        return;
    }

    db.announcements.unshift({ id:uid(), title, body, date:new Date().toISOString() });
    addActivity("📢", "Announcement published: " + title);

    document.getElementById("aTitle").value = "";
    document.getElementById("aBody").value = "";
    commit();
    showMessage("Announcement published.");
}

function deleteAnnouncement(id) {
    if (!confirm("Delete this announcement?")) return;
    db.announcements = db.announcements.filter(a => a.id !== id);
    commit();
}

function renderAnnouncements() {
    const box = document.getElementById("announcementContent");

    if (!db.announcements.length) {
        box.innerHTML = '<p class="empty">No announcements yet.</p>';
        return;
    }

    box.innerHTML = db.announcements.map(a =>
        '<div class="announce-item"><b>' + esc(a.title) + "</b>" + esc(a.body) +
        "<small>" + fmtDateTime(a.date) + "</small>" +
        (currentRole === "Admin" ? '<button class="mini-btn del" onclick="deleteAnnouncement(\'' + a.id + '\')">Delete</button>' : "") +
        "</div>"
    ).join("");
}

/* ---------- DASHBOARD ---------- */

function renderDashboard() {
    const inside = db.attendance.filter(a => !a.out).length;
    const items = db.inventory.reduce((sum, i) => sum + i.total, 0);
    const expiring = db.members.filter(m => memberStatus(m).label === "Expiring").length;

    document.getElementById("statMembers").textContent = db.members.length;
    document.getElementById("statInside").textContent = inside;
    document.getElementById("statItems").textContent = items;
    document.getElementById("statExpiring").textContent = expiring;

    const latest = db.announcements[0];
    document.getElementById("latestAnnouncement").innerHTML = latest
        ? '<div class="announce-item"><b>' + esc(latest.title) + "</b>" + esc(latest.body) + "<small>" + fmtDateTime(latest.date) + "</small></div>"
        : '<p class="empty">No announcements yet.</p>';

    const activities = db.activities.slice(0, 6);
    document.getElementById("activities").innerHTML = activities.length
        ? activities.map(a => '<div class="activity-item">' + a.icon + " " + esc(a.text) + "<small>" + fmtDateTime(a.time) + "</small></div>").join("")
        : '<p class="empty">No activity yet. Register a member or scan an RFID card.</p>';
}

/* ---------- REPORTS ---------- */

function renderReports() {
    const active = db.members.filter(m => memberStatus(m).label === "Active").length;
    const expiring = db.members.filter(m => memberStatus(m).label === "Expiring").length;
    const expired = db.members.filter(m => memberStatus(m).label === "Expired").length;
    const todayStr = new Date().toDateString();
    const visitsToday = db.attendance.filter(a => new Date(a.in).toDateString() === todayStr).length;
    const borrowedNow = db.borrows.filter(b => !b.returned).reduce((s, b) => s + b.qty, 0);

    const cards = [
        ["Total members", db.members.length],
        ["Active", active],
        ["Expiring (7 days)", expiring],
        ["Expired", expired],
        ["Inside now", db.attendance.filter(a => !a.out).length],
        ["Visits today", visitsToday],
        ["Item types", db.inventory.length],
        ["Items borrowed now", borrowedNow]
    ];

    document.getElementById("reportContent").innerHTML =
        '<p>Generated: ' + new Date().toLocaleString() + "</p>" +
        '<div class="report-grid">' +
        cards.map(c => "<div><small>" + c[0] + "</small><b>" + c[1] + "</b></div>").join("") +
        "</div>";
}

function downloadCSV(filename, rows) {
    const csv = rows.map(r => r.map(v => '"' + String(v == null ? "" : v).replace(/"/g, '""') + '"').join(",")).join("\n");
    const blob = new Blob([csv], { type:"text/csv" });
    const link = document.createElement("a");
    link.href = URL.createObjectURL(blob);
    link.download = filename;
    link.click();
    URL.revokeObjectURL(link.href);
}

function exportMembersCSV() {
    const rows = [["Name","RFID","Contact","Type","Expiry","Status"]];
    db.members.forEach(m => rows.push([m.name, m.rfid, m.contact, m.type, m.expiry, memberStatus(m).label]));
    downloadCSV("members.csv", rows);
}

function exportAttendanceCSV() {
    const rows = [["Member","Entry","Exit"]];
    db.attendance.forEach(a => rows.push([a.name, a.in, a.out || ""]));
    downloadCSV("attendance.csv", rows);
}

/* ---------- PROFILE (Members portal) ---------- */

function renderProfile() {
    const box = document.getElementById("profileContent");
    const m = getMember(viewAsId);

    if (!m) {
        box.innerHTML = '<p class="empty">No member selected. Ask staff to register you first.</p>';
        return;
    }

    const s = memberStatus(m);
    const visits = db.attendance.filter(a => a.memberId === m.id).length;
    const left = daysLeft(m);

    box.innerHTML =
        '<div class="profile-grid">' +
        "<div><small>Name</small><b>" + esc(m.name) + "</b></div>" +
        "<div><small>RFID</small><b>" + esc(m.rfid) + "</b></div>" +
        "<div><small>Contact</small><b>" + esc(m.contact || "-") + "</b></div>" +
        "<div><small>Membership</small><b>" + esc(m.type) + "</b></div>" +
        "<div><small>Expires</small><b>" + fmtDate(m.expiry) + "</b></div>" +
        '<div><small>Status</small><span class="badge ' + s.cls + '">' + s.label + (left >= 0 ? " (" + left + " days left)" : "") + "</span></div>" +
        "<div><small>Total visits</small><b>" + visits + "</b></div>" +
        "</div>";
}

/* ---------- SETTINGS ---------- */

function resetDemoData() {
    if (!confirm("Replace all current data with the sample data? Admin and Staff accounts are kept.")) return;
    db = seedData();
    users = users.filter(u => u.role !== "Members");   // old member accounts pointed at the old members
    saveUsers();
    commit();
    showMessage("Sample data restored.");
}

function clearAllData() {
    if (!confirm("Delete ALL members, inventory, attendance and announcements? Admin and Staff accounts are kept.")) return;
    db = { members:[], inventory:[], borrows:[], attendance:[], announcements:[], activities:[] };
    users = users.filter(u => u.role !== "Members");
    saveUsers();
    commit();
    showMessage("All data cleared.");
}

/* ---------- RENDER ALL ---------- */

function renderAll() {
    if (!currentRole) return;
    renderUsers();
    renderDashboard();
    renderMembers();
    renderInventory();
    renderAttendance();
    renderAnnouncements();
    renderReports();
    renderProfile();
}

/* ---------- START ---------- */

(function init() {
    try {
        const theme = localStorage.getItem("pickleball_theme");
        if (theme) document.documentElement.setAttribute("data-theme", theme);
    } catch (e) {}

    document.getElementById("rfidInput").addEventListener("keydown", e => {
        if (e.key === "Enter") scanRFID();
    });

    // any activity restarts the inactivity timer
    ["click","keydown","touchstart"].forEach(name => {
        document.addEventListener(name, resetIdle, { passive:true });
    });

    // This page is only for signed-in people.
    // login.html saves the session; no valid session means back to the login page.
    let user = null;
    try {
        const saved = JSON.parse(sessionStorage.getItem(SESSION_KEY));
        user = saved && users.find(u => u.username === saved.username);
    } catch (e) {}

    if (user) startSession(user);
    else location.replace("login.html");
})();


/* ===== DASHBOARD ENHANCEMENTS ===== */

document.addEventListener("DOMContentLoaded", () => {

    // Display current date
    const dateElement = document.getElementById("dashboardDate");

    if (dateElement) {
        dateElement.textContent =
            "📅 " + new Date().toLocaleDateString(undefined, {
                weekday: "long",
                month: "long",
                day: "numeric",
                year: "numeric"
            });
    }

    // Animate dashboard statistics
    document.querySelectorAll(".count-up").forEach((element) => {

        const target = Number(element.dataset.target);

        if (!Number.isFinite(target)) return;

        const duration = 900;
        const startTime = performance.now();

        const animate = (now) => {

            const progress = Math.min(
                (now - startTime) / duration,
                1
            );

            const eased = 1 - Math.pow(1 - progress, 3);

            element.textContent = Math.round(
                target * eased
            ).toLocaleString();

            if (progress < 1) {
                requestAnimationFrame(animate);
            }
        };

        requestAnimationFrame(animate);
    });

});
