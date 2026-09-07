function unavailable(name) {
  return () => {
    throw new Error(`Node fs.${name} is unavailable in the browser demo`);
  };
}

export default {
  existsSync: () => false,
  readFileSync: unavailable("readFileSync"),
  writeFileSync: unavailable("writeFileSync")
};
