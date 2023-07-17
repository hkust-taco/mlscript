declare interface Driver {
  watch(
    filename: string,
    workDir: string,
    outputDir: string,
    tsconfig: string,
    commonJS: boolean,
    expectTypeError: boolean
  );
  
  watch(
    filename: string,
    workDir: string,
    outputDir: string,
    commonJS: boolean,
    expectTypeError: boolean
  );
}

declare const driver: Driver
export = driver;
