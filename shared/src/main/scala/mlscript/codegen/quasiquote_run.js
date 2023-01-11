function run(s_expr, context) {
    let program_str = ``;
    var var_symbol_mapping = {};

    switch(s_expr[0]) {
        case "Var":
            // do the mapping 
            program_str = s_expr[1];
            break;
        case "App":
            program_str = run(s_expr[2]) + s_expr[1] + run(s_expr[3]);
            break;
        case "Lam":
            let param_str = run(s_expr[1]);
            program_str = `(${param_str.slice(1, -1)}) => ${run(s_expr[2])}`;
            break;
        case "Tup":
            let tup_array = s_expr.slice(1).map(function(value) {return run(value)} );
            program_str = `[${tup_array.toString()}]`;
            break;
        case "Rcd": 
            let rcd_array = s_expr.slice(1).map(function([key,value]) {return `${run(key)} : ${run(value)}`});
            program_str = `{${rcd_array.toString()}}`
            break;
        case "Sel": //const record1 = {x:1}; record1.x;
            program_str = `TODO: Sel`;
            break;
        case "If":
            program_str = `if (${run(s_expr[1])}) { ${run(s_expr[2])} } else { ${run(s_expr[3])} }`;
            break;
        case "Let":
            program_str = `const ${run(s_expr[1])} = ${run(s_expr[2])}; ${run(s_expr[3])}`;
            break;
        case "Assign":
            program_str = `TODO: Assign`;
            break;
        case "Subs":
            program_str = `${run(s_expr[1])}[${run(s_expr[2])}]`;
            break;
        case "UnitLit":
            program_str = `TODO: UnitLit`;
            break;
        case "StrLit":
            program_str = `'${s_expr[1]}'`
            break;
        default: // IntLit, DecLit
            program_str = s_expr[0];
    }
    return program_str;
}