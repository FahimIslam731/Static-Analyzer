// ECS 261 Final Project
// Tests.dfy

include "Types.dfy" 
include "StaticAnalyzer.dfy" 

module Tests{
    import opened StaticAnalyzer
    import opened Types

    method TestCaseSimpleArithmetic(){
        /*
        v := 4 + 4;
        v := v / 2;
        */
        var stmt1 := Assign("v", Add(Const(4), Const(4)));
        var stmt2 := Assign("v", Div(Var("v"), Const(2)));
        var stmt := Seq(stmt1, stmt2);
        var env := map[];
        
        var safe := analyze_program(stmt, env);
        assert safe;
        AnalyzeProgramSound(stmt, env);

        match exec_stmt(stmt, env)
        case Ok(envOut) => assert envOut["v"] == 4;
        case Err(e) => assert false;
    }

    method TestCaseUninitVarErr(){
        /*
        y := x + 1;
        */
        var stmt := Assign("y", Add(Var("x"), Const(1)));
        var env := map[];

        var safe := analyze_program(stmt, env);
        assert !safe;
        AnalyzeProgramSound(stmt, env);
        
        match exec_stmt(stmt, env)
        case Ok(envOut) => assert false;
        case Err(e) => assert e == UninitializedVar("x");
    }

    method TestCaseSimpleIf(){
        /*
        if(1){
            x := 1;
        } else{
            x := 0;
        }
        */
        var cond_expr := Const(1);
        var stmt_then := Assign("x", Const(1));
        var stmt_else := Assign("x", Const(0));
        var stmt := If(cond_expr, stmt_then, stmt_else);
        var env := map[];

        var safe := analyze_program(stmt, env);
        assert safe;
        AnalyzeProgramSound(stmt, env);
        
        match exec_stmt(stmt, env)
        case Ok(envOut) => assert envOut["x"] == 1;
        case Err(e) => assert false;
    }

    method TestCaseIfCasePruning(){
        /*
        if(1){
            x := 1;
        } else{
            y := 0;
        }
        z := x;
        */
        var cond_expr := Const(1);
        var stmt_then := Assign("x", Const(1));
        var stmt_else := Assign("y", Const(0));
        var if_stmt := If(cond_expr, stmt_then, stmt_else);
        var stmt := Seq(if_stmt, Assign("z", Var("x")));
        var env := map[];
        
        var safe := analyze_program(stmt, env);
        assert safe;
        AnalyzeProgramSound(stmt, env);

        match exec_stmt(stmt, env)
        case Ok(envOut) => assert envOut["x"] == 1;
        case Err(e) => assert false;
    }

    method TestCaseAdditionInDenom(){
        /*
        z := 12 / (2 + 2);
        */
        var stmt := Assign("z", Div(Const(12), Add(Const(2), Const(2))));
        var env := map[];
        
        var safe := analyze_program(stmt, env);
        assert safe;
        AnalyzeProgramSound(stmt, env);
        
        match exec_stmt(stmt, env)
        case Ok(envOut) => assert envOut["z"] == 3;
        case Err(e) => assert false;
    }

    method TestCaseArithmeticConditionBranch(){
        /*
        if(1 + (-1)){
            v := 30;
        } else{
            v := 4 * 4;
            v := v - 2;
        }
        */
        var cond := Add(Const(1), Const(-1));
        var stmt1 := Assign("v", Mul(Const(4), Const(4)));
        var stmt2 := Assign("v", Sub(Var("v"), Const(2)));
        var stmt := If(cond, Assign("v", Const(30)), Seq(stmt1, stmt2));
        var env := map[];
        
        var safe := analyze_program(stmt, env);
        assert safe;
        AnalyzeProgramSound(stmt, env);

        match exec_stmt(stmt, env)
        case Ok(envOut) => assert envOut["v"] == 14;
        case Err(e) => assert false;
    }

    method TestCaseModulo(){
        /*
        v := 4 + 4;
        v := v % 2;
        */
        var stmt1 := Assign("v", Add(Const(4), Const(4)));
        var stmt2 := Assign("v", Mod(Var("v"), Const(2)));
        var stmt := Seq(stmt1, stmt2);
        var env := map[];
        
        var safe := analyze_program(stmt, env);
        assert safe;
        AnalyzeProgramSound(stmt, env);

        match exec_stmt(stmt, env)
        case Ok(envOut) => assert envOut["v"] == 0;
        case Err(e) => assert false;
    }

    method TestCaseSimpleDivByZero(){
        /*
        v := 0;
        v := 1 / v;
        */
        var s1 := Assign("v", Const(0));
        var s2 := Assign("v", Div(Const(1), Var("v")));
        var stmt := Seq(s1, s2);
        var env := map[];
       
        var safe := analyze_program(stmt, env);
        assert !safe;
        AnalyzeProgramSound(stmt, env);
        
        match exec_stmt(stmt, env)
        case Ok(envOut) => assert false;
        case Err(e) => assert e == DivByZero;
    }

    method TestCasePruningElseBranchError(){
        /*
        if (1) then (x := 5) else (x := 1 / 0);
        z := x;
        */
        var then_stmt := Assign("x", Const(5));
        var else_stmt := Assign("x", Div(Const(1), Const(0)));
        var s1 := If(Const(1), then_stmt, else_stmt);
        var s2 := Assign("z", Var("x"));
        var stmt := Seq(s1, s2);
        var env := map[];
        

        var safe := analyze_program(stmt, env);
        assert safe;
        AnalyzeProgramSound(stmt, env);

        match exec_stmt(stmt, env)
        case Ok(envOut) => assert envOut["z"] == 5;
        case Err(e) => assert false;
    }

    method TestCaseIncompleteness(){
        /*
        z := 2 + (-1);
        if (z) then (x := 5) else (x := 1 / 0)
        z := z + x;
        */
        var cond := Assign("z", Add(Const(2), Const(-1)));
        var then_stmt := Assign("x", Const(5));
        var else_stmt := Assign("x", Div(Const(1), Const(0)));
        var s1 := If(Var("z"), then_stmt, else_stmt);
        var s2 := Assign("z", Add(Var("z"), Var("x")));
        var stmt := Seq(cond, Seq(s1, s2));
        var env := map[];

        var safe := analyze_program(stmt, env);
        assert !safe;
        AnalyzeProgramSound(stmt, env);

        match exec_stmt(stmt, env)
        case Ok(envOut) => assert envOut["z"] == 6;
        case Err(e) => assert false;
    }

    method TestCaseLoop(){
        /*
        z := 4;
        loop(z){
            z := z + 1;
        }
        */
        var stmt1 := Assign("z", Const(4));
        var stmt2 := Loop(Var("z"), Assign("z", Add(Var("z"), Const(1))));
        var stmt := Seq(stmt1, stmt2);
        var env := map[];
        
        var safe := analyze_program(stmt, env);
        assert safe;
        AnalyzeProgramSound(stmt, env);
        
        match exec_stmt(stmt, env)
        case Ok(envOut) => assert envOut["z"] == 8;
        case Err(e) => assert false;
    }

    method TestCaseLoopIncomplete(){
        /*
        z := 4;
        x := 0;
        loop(z){
            x := x + 1;
        }
        */
        var stmt1 := Assign("z", Const(4));
        var stmt2 := Assign("x", Const(0));
        var stmt3 := Loop(Var("z"), Assign("x", Add(Var("x"), Const(1))));
        var stmt := Seq(stmt1, Seq(stmt2, stmt3));
        var env := map[];
        
        var safe := analyze_program(stmt, env);
        assert !safe;
        AnalyzeProgramSound(stmt, env);
        
        match exec_stmt(stmt, env)
        case Ok(envOut) => assert envOut["x"] == 4;
        case Err(e) => assert false;
    }

    // Add your own test programs here!
    // Follow the format above, explained in README.md.
}