let currentFilter = "all";
let currentRoleFilter = "all";
let loadedFolders = [];

const statuses = ["direct", "analogue", "not-needed", "ignored", "foundational", "qol"];

function percent(part, total) {
  return total === 0 ? 0 : Math.round((part / total) * 1000) / 10;
}

function escapeHtml(text) {
  return String(text ?? "")
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#39;");
}

function parseRows(text, ignored = false) {
  return text
    .split(/\r?\n/)
    .filter((line) => line.trim().length > 0)
    .map((line) => {
      const [rocq = "", arend = "", relation = "missing", role = "qol", note = ""] = line.split("\t");
      return {
        rocq: rocq.trim(),
        arend: arend.trim(),
        status: ignored ? "ignored" : relation.trim(),
        role: role.trim(),
        note: note.trim(),
      };
    });
}

function addStats(item) {
  for (const status of statuses) {
    item[status] = item.rows
      ? item.rows.filter((row) => row.status === status || (row.status === "missing" && row.role === status)).length
      : item.files.reduce((sum, file) => sum + file[status], 0);
  }
  item.total = item.rows ? item.rows.length : item.files.reduce((sum, file) => sum + file.total, 0);
  return item;
}

async function loadFile(file) {
  const response = await fetch(file.path);
  if (!response.ok) throw new Error(`Could not load ${file.path}`);
  return addStats({ ...file, rows: parseRows(await response.text(), file.ignored) });
}

async function loadData() {
  return Promise.all(
    window.ROCQ_MANIFEST.map(async (folder) =>
      addStats({ ...folder, files: await Promise.all(folder.files.map(loadFile)) }),
    ),
  );
}

function sectionStats(item) {
  if (item.ignored) return `out of scope ${item.total}/${item.total}`;
  const implemented = item.direct + item.analogue;
  const relevant = item.total - item["not-needed"] - item.ignored;
  return `${implemented}/${relevant} (${percent(implemented, relevant)}%)`;
}

function bar(item, className = "mini-bar") {
  return `
    <span class="${className}">
      ${statuses.map((status) => `<span class="bar-fill ${status}" style="width:${percent(item[status], item.total)}%"></span>`).join("")}
    </span>
  `;
}

function statusLabel(row) {
  if (row.status === "missing") return row.role === "foundational" ? "missing: foundational" : "missing: QoL";
  return {
    direct: "direct port",
    analogue: "Arend analogue",
    "not-needed": "not needed",
    ignored: "out of scope",
  }[row.status];
}

function renderTableRows(rows) {
  return rows
    .map((row) => `
      <tr class="entry ${row.status} ${row.role}" data-name="${escapeHtml(row.rocq)}" data-arend="${escapeHtml(row.arend)}" data-note="${escapeHtml(row.note)}">
        <td>${escapeHtml(row.rocq)}</td>
        <td><span class="badge badge-${row.status} badge-${row.role}">${statusLabel(row)}</span></td>
        <td><span class="role role-${row.role}">${row.role === "foundational" ? "foundational" : "quality of life"}</span></td>
        <td><div class="detail-scroll">${escapeHtml(row.arend)}</div></td>
        <td><div class="detail-scroll note">${escapeHtml(row.note)}</div></td>
      </tr>
    `)
    .join("");
}

function renderFile(file) {
  return `
    <div class="file-section">
      <div class="section-header" onclick="toggle(this)">
        <span class="arrow">&#9654;</span>
        <code class="file-name">${escapeHtml(file.name)}</code>
        <a class="file-link" href="${escapeHtml(file.source)}" target="_blank" onclick="event.stopPropagation()">[src]</a>
        <span class="section-stats">${sectionStats(file)}</span>
        ${bar(file)}
      </div>
      <table class="file-table">
        <colgroup>
          <col class="col-name"><col class="col-status"><col class="col-role"><col class="col-arend"><col class="col-note">
        </colgroup>
        <thead><tr><th>Rocq Name</th><th>Porting status</th><th>Role</th><th>Arend Definition</th><th>Comment</th></tr></thead>
        <tbody>${renderTableRows(file.rows)}</tbody>
      </table>
    </div>
  `;
}

function renderFolder(folder) {
  return `
    <div class="folder-section${folder.ignored ? " ignored-section" : ""}">
      <div class="section-header" onclick="toggle(this)">
        <span class="arrow">&#9654;</span>
        <code class="folder-name">${escapeHtml(folder.name)}</code>
        ${folder.ignoreReason ? `<span class="ignore-reason">${escapeHtml(folder.ignoreReason)}</span>` : ""}
        <span class="section-stats">${sectionStats(folder)}</span>
        ${bar(folder)}
      </div>
      <div class="folder-children">${folder.files.map(renderFile).join("")}</div>
    </div>
  `;
}

function render(folders) {
  const summary = addStats({ files: folders });
  const implemented = summary.direct + summary.analogue;
  const relevant = summary.total - summary["not-needed"] - summary.ignored;
  const files = folders.reduce((sum, folder) => sum + folder.files.length, 0);

  for (const id of ["total", "direct", "analogue", "not-needed", "ignored", "foundational", "qol"]) {
    document.getElementById(`${id}-count`).textContent = summary[id] ?? summary.total;
  }
  document.getElementById("file-count").textContent = files;
  document.getElementById("progress-count").textContent = `${percent(implemented, relevant)}%`;
  document.getElementById("progress-bar").innerHTML = bar(summary, "progress-segments");
  document.getElementById("content").innerHTML = folders.map(renderFolder).join("");
  applyFilters();
}

function toggle(header) {
  header.parentElement.classList.toggle("open");
}

function setFilter(filter) {
  currentFilter = filter;
  document.querySelectorAll("[data-status-filter]").forEach((button) => {
    button.classList.toggle("active", button.dataset.statusFilter === filter);
  });
  applyFilters();
}

function setRoleFilter(filter) {
  currentRoleFilter = filter;
  document.querySelectorAll("[data-role-filter]").forEach((button) => {
    button.classList.toggle("active", button.dataset.roleFilter === filter);
  });
  applyFilters();
}

function applyFilters() {
  const search = document.querySelector(".search").value.trim().toLowerCase();

  document.querySelectorAll(".entry").forEach((entry) => {
    const statusMatch = currentFilter === "all" || entry.classList.contains(currentFilter);
    const roleMatch = currentRoleFilter === "all" || entry.classList.contains(currentRoleFilter);
    const text = `${entry.dataset.name} ${entry.dataset.arend} ${entry.dataset.note}`.toLowerCase();
    entry.classList.toggle("hidden", !(statusMatch && roleMatch && (!search || text.includes(search))));
  });

  document.querySelectorAll(".file-section").forEach((file) => file.classList.toggle("hidden", !file.querySelector(".entry:not(.hidden)")));
  document.querySelectorAll(".folder-section").forEach((folder) => folder.classList.toggle("hidden", !folder.querySelector(".file-section:not(.hidden)")));
}

loadData()
  .then((folders) => {
    loadedFolders = folders;
    render(loadedFolders);
  })
  .catch((error) => {
    document.getElementById("content").innerHTML = `<p class="load-error">${escapeHtml(error.message)}. Serve the docs directory over HTTP so the browser can fetch the .txt files.</p>`;
  });
