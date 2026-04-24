function fileURLToPath(value) {
  const url = value instanceof URL ? value : new URL(String(value));
  return decodeURIComponent(url.pathname);
}

export default { fileURLToPath };
