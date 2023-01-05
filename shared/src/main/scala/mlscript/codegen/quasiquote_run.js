function run(s_expr) { // TODO: handle context 
    let program_str = ``;
    const node_symbol_mapping = {
        "Var" : "&",
        "App" : "@",
        "Lam" : "=>",
        "Tup" : "#",
        "StrLit" : "s",
    };
    var var_symbol_mapping = {}; // TODO: handle hygiene in Var 

    switch(s_expr[0]) {
        case node_symbol_mapping["Var"]:
            // do the mapping 
            program_str = s_expr[1];
            break;
        case node_symbol_mapping["App"]:
            program_str = run(s_expr[2]) + s_expr[1] + run(s_expr[3]);
            break;
        case node_symbol_mapping["Lam"]:
            let param_str = run(s_expr[1]);
            program_str = `(${param_str.slice(1, -1)}) => ${run(s_expr[2])}`;
            break;
        case node_symbol_mapping["Tup"]:
            let tup_array = s_expr.slice(1).map(function(value){return run(value).toString()});
            program_str = `[${tup_array.toString()}]`;
            break;
        case node_symbol_mapping["StrLit"]:
            program_str = `'${s_expr[1]}'`
            break;
        default: // IntLit, DecLit
            program_str = s_expr[0];
    }
    return program_str;
}

const test1 = [ '@', '+', [ '1' ], [ '@', '*', [ '2' ], [ '3' ] ] ]; // code"1 + 2 * 3"
let res1 = run(test1);
const test2 = [ '&', 'x' ]; // code"x"
let res2 = run(test2);
const test3 = [ '@', '+', [ '&', 'y' ], [ '1' ] ]; // code"y + 1"
let res3 = run(test3);
// code"(x,y) => x + 3"
const test4 = ['=>',[ '#', [ '&', 'x' ], [ '&', 'y' ] ],[ '@', '+', [ '&', 'x' ], [ '3' ] ]];
let res4 = run(test4);
const test5 = [ '#', [ '&', 'x' ], [ '&', 'y' ] ];
let res5 = run(test5);
const test6 = ['s', 'string'];
let res6 = run(test6);
const test7 = [ '#', ['s', 'strings'], ['s', 'stringss'] ];
let res7 = run(test7);