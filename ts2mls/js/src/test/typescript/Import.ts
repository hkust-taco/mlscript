import "./Dependency"
import f from "./Dependency"
import { A } from "./Dependency"
import { A as B } from "./Dependency"
import * as D from "./Dependency"
import type { A as C } from "./Dependency"


const t = f();

const a = new A();
const b = new B();
let c: C
const d = D.default();
