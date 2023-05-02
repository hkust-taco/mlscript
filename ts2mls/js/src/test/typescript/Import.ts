import "./Dependency"
import f from "./Dependency"
import { A } from "./Dependency"
import { B as BB } from "./Dependency"
import * as D from "./Dependency"
import type { C as CC } from "./Dependency"


const t = f();

const a = new A();
const b = new BB();
let c: CC
const d = new D.D();
const dd = D.default();
