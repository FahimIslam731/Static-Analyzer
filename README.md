# Static-Analyzer
Static Analyzer, final project for ECS 261

## Getting started.
Verify the files

```bash
dafny verify Types.dfy StaticAnalyzer.dfy Tests.dfy
```

## Add your own test cases/programs.
Create your own dafny test file, you can copy the starter code below.

```dafny
include "Types.dfy" 
include "StaticAnalyzer.dfy" 

module Tests{
    import opened StaticAnalyzer
    import opened Types

    // write tests here
}
```

```dafny
    method TestCaseNAME(){
        /*
        Put the readable syntax version of your program here.
        */
        var stmt := // Fill this in. default is "Skip()"
        var env := // Fill this in. default is "map[];"

        var safe := AnalyzeProgram(stmt, env);
        assert safe; // or !safe if your prog is potentially erroneous, dafny will give an error.
        AnalyzeProgramSound(stmt, env);

        match ExecStmt(stmt, env)
        case Ok(envOut) => assert // this will have either Ok(envOut) or false, you can verify the value here
        case Err(e) => assert // this will have either a Err(RuntimeError) or false, you can verify the error type here
    }
```

Reference Types.dfy for the types of statements/expressions and Tests.py for examples.
