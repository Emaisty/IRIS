let currentFilter = "all";
let loadedFolders = [];

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

function parseRows(text) {
  return text
    .split(/\r?\n/)
    .filter((line) => line.trim().length > 0)
    .map((line) => {
      const [rocq = "", arend = ""] = line.split("\t");
      const status = arend.trim() ? "ported" : "missing";
      return {
        rocq: rocq.trim(),
        arend: arend.trim(),
        status,
      };
    });
}

async function loadFile(file) {
  const response = await fetch(file.path);
  if (!response.ok) {
    throw new Error(`Could not load ${file.path}`);
  }
  const rows = parseRows(await response.text());
  return {
    ...file,
    rows,
    total: rows.length,
    ported: rows.filter((row) => row.status === "ported").length,
  };
}

async function loadData() {
  const folders = await Promise.all(
    window.ROCQ_MANIFEST.map(async (folder) => {
      const files = await Promise.all(folder.files.map(loadFile));
      return {
        ...folder,
        files,
        total: files.reduce((sum, file) => sum + file.total, 0),
        ported: files.reduce((sum, file) => sum + file.ported, 0),
      };
    }),
  );
  return folders;
}

function sectionStats(ported, total) {
  return `${ported}/${total} (${percent(ported, total)}%)`;
}

function miniBar(ported, total) {
  return `
    <span class="mini-bar">
      <span class="mini-bar-fill ported" style="width:${percent(ported, total)}%"></span>
    </span>
  `;
}

function renderTableRows(rows) {
  return rows
    .map((row) => {
      return `
        <tr class="entry ${row.status}" data-name="${escapeHtml(row.rocq)}" data-arend="${escapeHtml(row.arend)}">
          <td>${escapeHtml(row.rocq)}</td>
          <td><span class="badge badge-${row.status}"></span></td>
          <td><div class="detail-scroll">${escapeHtml(row.arend)}</div></td>
        </tr>
      `;
    })
    .join("");
}

function renderFile(file) {
  return `
    <div class="file-section">
      <div class="section-header" onclick="toggle(this)">
        <span class="arrow">&#9654;</span>
        <code class="file-name">${escapeHtml(file.name)}</code>
        <a class="file-link" href="${escapeHtml(file.source)}" target="_blank" onclick="event.stopPropagation()">[src]</a>
        <span class="section-stats">${sectionStats(file.ported, file.total)}</span>
        ${miniBar(file.ported, file.total)}
      </div>
      <table class="file-table">
        <colgroup>
          <col class="col-name">
          <col class="col-status">
          <col class="col-arend">
        </colgroup>
        <thead>
          <tr>
            <th>Rocq Name</th>
            <th>Status</th>
            <th>Arend Definition</th>
          </tr>
        </thead>
        <tbody>${renderTableRows(file.rows)}</tbody>
      </table>
    </div>
  `;
}

function renderFolder(folder) {
  return `
    <div class="folder-section">
      <div class="section-header" onclick="toggle(this)">
        <span class="arrow">&#9654;</span>
        <code class="folder-name">${escapeHtml(folder.name)}</code>
        <span class="section-stats">${sectionStats(folder.ported, folder.total)}</span>
        ${miniBar(folder.ported, folder.total)}
      </div>
      <div class="folder-children">
        ${folder.files.map(renderFile).join("")}
      </div>
    </div>
  `;
}

function render(folders) {
  const total = folders.reduce((sum, folder) => sum + folder.total, 0);
  const ported = folders.reduce((sum, folder) => sum + folder.ported, 0);
  const files = folders.reduce((sum, folder) => sum + folder.files.length, 0);
  const missing = total - ported;
  const progress = percent(ported, total);

  document.getElementById("total-count").textContent = total;
  document.getElementById("ported-count").textContent = ported;
  document.getElementById("missing-count").textContent = missing;
  document.getElementById("folder-count").textContent = folders.length;
  document.getElementById("file-count").textContent = files;
  document.getElementById("progress-count").textContent = `${progress}%`;
  document.getElementById("progress-fill").style.width = `${progress}%`;

  document.getElementById("content").innerHTML = folders.map(renderFolder).join("");
  applyFilters();
}

function toggle(header) {
  header.parentElement.classList.toggle("open");
}

function setFilter(filter) {
  currentFilter = filter;
  document.querySelectorAll(".filter-btn").forEach((button) => {
    button.classList.toggle("active", button.textContent === filter);
  });
  applyFilters();
}

function applyFilters() {
  const search = document.querySelector(".search").value.trim().toLowerCase();

  document.querySelectorAll(".entry").forEach((entry) => {
    const statusMatch = currentFilter === "all" || entry.classList.contains(currentFilter);
    const text = `${entry.dataset.name} ${entry.dataset.arend}`.toLowerCase();
    const searchMatch = !search || text.includes(search);
    entry.classList.toggle("hidden", !(statusMatch && searchMatch));
  });

  document.querySelectorAll(".file-section").forEach((file) => {
    const hasVisibleRows = !!file.querySelector(".entry:not(.hidden)");
    file.classList.toggle("hidden", !hasVisibleRows);
  });

  document.querySelectorAll(".folder-section").forEach((folder) => {
    const hasVisibleFiles = !!folder.querySelector(".file-section:not(.hidden)");
    folder.classList.toggle("hidden", !hasVisibleFiles);
  });
}

loadData()
  .then((folders) => {
    loadedFolders = folders;
    render(loadedFolders);
  })
  .catch((error) => {
    document.getElementById("content").innerHTML = `
      <p class="load-error">
        ${escapeHtml(error.message)}. Serve the docs directory over HTTP so the browser can fetch the .txt files.
      </p>
    `;
  });
