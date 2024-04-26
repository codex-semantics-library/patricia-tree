/* The browsers interpretation of the CORS origin policy prevents to run
   webworkers from javascript files fetched from the file:// protocol. This hack
   is to workaround this restriction. */
function createWebWorker() {
  var searchs = search_urls.map((search_url) => {
    let parts = document.location.href.split("/");
    parts[parts.length - 1] = search_url;
    return '"' + parts.join("/") + '"';
  });
  blobContents = ["importScripts(" + searchs.join(",") + ");"];
  var blob = new Blob(blobContents, { type: "application/javascript" });
  var blobUrl = URL.createObjectURL(blob);

  var worker = new Worker(blobUrl);
  URL.revokeObjectURL(blobUrl);

  return worker;
}

var worker;
var waiting = 0;

function wait() {
  waiting = waiting + 1;
  document.querySelector(".search-snake").classList.add("search-busy");
}

function stop_waiting() {
  if (waiting > 0) waiting = waiting - 1;
  else waiting = 0;
  if (waiting == 0) {
    document.querySelector(".search-snake").classList.remove("search-busy");
  }
}

document.querySelector(".search-bar").addEventListener("focus", (ev) => {
  if (typeof worker == "undefined") {
    worker = createWebWorker();
    worker.onmessage = (e) => {
      stop_waiting();
      let results = e.data;
      let search_results = document.querySelector(".search-result");
      search_results.innerHTML = "";
      let f = (entry) => {
        let search_result = document.createElement("a");
        search_result.classList.add("search-entry");
        // MANUAL EDIT: change the URL to match our scheme:
        // ie. no package level in URL, instead replace it with a version level
        // See https://github.com/art-w/sherlodoc/issues/41 for a discussion on this
        search_result.href =
          // removing leading "../" that would take us back to the package level
          // The url is instead relative to the library toplevel
          base_url.replace(/^\.\.\//, "") +
          // Removing package-name from full URL (given relative to the package level)
          entry.url.replace(/^patricia\-tree\//, "");
        search_result.innerHTML = entry.html;
        search_results.appendChild(search_result);
      };
      results.forEach(f);
      let search_request = document.querySelector(".search-bar").value;
      if (results.length == 0 && search_request != "") {
        let no_result = document.createElement("div");
        no_result.classList.add("search-no-result");
        no_result.innerText = "No result...";
        search_results.appendChild(no_result);
      }
    };
  }
});

document.querySelector(".search-bar").addEventListener("input", (ev) => {
  wait();
  worker.postMessage(ev.target.value);
});
