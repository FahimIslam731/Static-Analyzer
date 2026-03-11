include "StaticAnalyzer.dfy" 

module Tests{
    import opened StaticAnalyzer

    method TestCase1(){
        /*
        v := 4 + 4;
        v := v / 2;
        */
        var stmt1 := Assign("v", Add(Const(4), Const(4)));
        var stmt2 := Assign("v", Div(Var("v"), Const(2)));
        var stmt3 := Seq(stmt1, stmt2);
        var env := map[];
        var state := map[];
        
        AnalyzeProgramSound(stmt3);
        assert AnalyzeStmt(stmt3, state).0;
        match ExecStmt(stmt3, env)
        case Ok(env1) => assert env1["v"] == 4;
        case Err(e1) => assert false;
    }

    method TestCase2(){
        /*
        y := x + 1;
        */
        var stmt := Assign("y", Add(Var("x"), Const(1)));
        var state := map[];
        assert !AnalyzeStmt(stmt, state).0;
        var env := map[];
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert false;
        case Err(e1) => assert e1 == UninitializedVar("x");
    }

    method TestCase3(){
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
        var state := map[];

        AnalyzeProgramSound(stmt);

        assert AnalyzeStmt(stmt, state).0;
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["x"] == 1;
        case Err(e1) => assert false;
    }

    method TestCase4(){
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
        var state := map[];

        AnalyzeProgramSound(stmt);

        assert AnalyzeStmt(stmt, state).0;    
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["x"] == 1;
        case Err(e1) => assert false;
    }

    method TestCase5(){
        /*
        z := 1 / 0;
        */
        var stmt := Assign("z", Div(Const(1), Const(0)));
        var env := map[];
        var state := map[];

        assert !AnalyzeStmt(stmt, state).0;
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert false;
        case Err(e1) => assert e1 == DivByZero();
    }

    method TestCase6(){
        /*
        z := 12 / (2 + 2);
        */
        var stmt := Assign("z", Div(Const(12), Add(Const(2), Const(2))));
        var env := map[];
        var state := map[];

        assert !AnalyzeStmt(stmt, state).0;
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["z"] == 3;
        case Err(e1) => assert false;
    }

    method TestCase7(){
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
        var stmt3 := If(cond, Assign("v", Const(30)), Seq(stmt1, stmt2));
        var state := map[];
        
        assert AnalyzeStmt(stmt3, state).0;
        var env := map[];
        match ExecStmt(stmt3, env)
        case Ok(env1) => assert env1["v"] == 14;
        case Err(e1) => assert false;
    }

    method TestCase8(){
        /*
        v := 4 + 4;
        v := v % 2;
        */
        var stmt1 := Assign("v", Add(Const(4), Const(4)));
        var stmt2 := Assign("v", Mod(Var("v"), Const(2)));
        var stmt3 := Seq(stmt1, stmt2);
        var env := map[];
        var state := map[];
        
        AnalyzeProgramSound(stmt3);
        assert AnalyzeStmt(stmt3, state).0;
        match ExecStmt(stmt3, env)
        case Ok(env1) => assert env1["v"] == 0;
        case Err(e1) => assert false;
    }

    method TestCaseDivByZero(){
        /*
        v := 0;
        v := 1 / v;
        */
        var s1 := Assign("v", Const(0));
        var s2 := Assign("v", Div(Const(1), Var("v")));
        var stmt := Seq(s1, s2);
        var env := map[];
        var state := map[];
        
        var safe := AnalyzeStmt(stmt, state).0;
        assert !safe;
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert false;
        case Err(e1) => assert e1 == DivByZero;
    }

    method TestCasePruning(){
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
        var state := map[];
        var safe := AnalyzeStmt(stmt, state).0;
        assert safe;
        AnalyzeProgramSound(stmt);
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["z"] == 5;
        case Err(e1) => assert false;
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
        var state := map[];
        var safe := AnalyzeStmt(stmt, state).0;
        assert !safe;
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["z"] == 6;
        case Err(e1) => assert false;
    }

    method TestCaseOverflow(){
        /*
        x := 10e17 + (-1);
        if (x) then (y := 3) else (z := )
        x := x + y
        */
        var cond := Assign("x", Add(Const(1000000000000000000), Const(-1)));
        var then_stmt := Assign("y", Const(3));
        var else_stmt := Assign("z", Const(2));
        var s1 := If(Var("x"), then_stmt, else_stmt);
        var s2 := Assign("x", Add(Var("x"), Var("y")));
        var stmt := Seq(cond, Seq(s1, s2));
        var env := map[];
        var state := map[];
        var safe := AnalyzeStmt(stmt, state).0;
        assert !safe;
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["x"] == 1000000000000000002;
        case Err(e1) => assert false;
    }
}