function trimSlashes(part) {
  return String(part).replace(/^\/+|\/+$/g, "");
}

function join(...parts) {
  const absolute = String(parts[0] ?? "").startsWith("/");
  const path = parts.filter(part => part !== "").map(trimSlashes).filter(Boolean).join("/");
  return (absolute ? "/" : "") + path;
}

function dirname(file) {
  const text = String(file);
  const index = text.lastIndexOf("/");
  return index < 0 ? "." : text.slice(0, index) || "/";
}

function relative(base, target) {
  const baseText = String(base).replace(/\/+$/, "");
  const targetText = String(target);
  return targetText.startsWith(baseText)
    ? targetText.slice(baseText.length).replace(/^\/+/, "")
    : targetText;
}

function parse(file) {
  const text = String(file);
  const base = text.slice(text.lastIndexOf("/") + 1);
  const extIndex = base.lastIndexOf(".");
  const ext = extIndex > 0 ? base.slice(extIndex) : "";
  const name = ext ? base.slice(0, -ext.length) : base;
  return { root: text.startsWith("/") ? "/" : "", dir: dirname(text), base, ext, name };
}

export default { dirname, join, parse, relative };
