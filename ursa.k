/*
K definition of the Ursa IR used for unit analysis.

Author: David Lazar
*/

module URSA-SYNTAX

    syntax Type
      ::= "real"

    syntax Declarator
      ::= Id
        | Declarator "{" UnitExp "}"

    syntax InitDeclarator
      ::= Declarator
        | Declarator "=" Exp

    syntax InitDeclarators
      ::= InitDeclarator
        | InitDeclarators "," InitDeclarator

    syntax UnitAtom
      ::= "#"         // dimensionless
        | Id          // physical unit
        | "`" K       // program variable
        | "?" Int     // fresh unit

    syntax UnitExp
      ::= UnitAtom
        | UnitAtom "^" Int      [right]
        > UnitExp UnitExp       [assoc, left]
        > UnitExp "/" UnitExp   [assoc, left]

    syntax Decl
      ::= Type InitDeclarators

    syntax Exp
      ::= Id
        | Int
        | Float
        | Float "{" UnitExp "}"
        | "(" Exp ")"       [bracket]
        | Exp "^" Exp       [strict(1), right]
        > left:
          Exp "*" Exp       [strict, left]
        | Exp "/" Exp       [strict]
        > left:
          Exp "+" Exp       [strict]
        | Exp "-" Exp       [strict]

    syntax Stmt
      ::= Decl ";"
        | Exp ";"
        | Id "=" Exp ";"    [strict(2)]

    // TODO conditionals: needed for dynamic semantics, but probably not for unit analysis
    // TODO loops: needed for unit analysis in rare cases, such as computing geometric mean

    syntax Stmts ::= Stmt | Stmt Stmts

endmodule

//@ Units form an abelian group with dimensionless (empty map) as the identity.
module URSA-UNITS
    imports URSA-SYNTAX
    imports RATIONALS

    syntax Unit
      ::= "{" Map "}"
        | Unit "^u" Rat      [latex({#1}^{#2})]
        > Unit "*u" Unit     [left, latex({#1}\times{#2})]
        | Unit "/u" Unit     [left, latex({#1}/{#2})]

    syntax Unit ::= "unit" "(" UnitExp ")" [function]

    rule unit(U1 U2) => unit(U1) *u unit(U2)
    rule unit(U1 / U2) => unit(U1) /u unit(U2)
    rule unit(U^I) => { U |-> I }
    rule unit(X:Id) => { X |-> 1 }
    rule unit(` X) => { ` X |-> 1 }
    rule unit(? I) => { ? I |-> 1 }
    rule unit(#) => {.}


    rule { (X |-> N)  Us } ^u M:Rat => { X |-> N *Rat M } *u ({ Us } ^u M)
        [anywhere]
    rule { . } ^u M:Rat => { . }
        [anywhere]

    rule
        { U1 } *u { U2 } => { U1 U2 }
        [anywhere]

    rule
        { U1 } /u { U2 } => { U1 } *u ({ U2 } ^u -1)
        [anywhere]

    rule
        { (X |-> N X |-> M => X |-> (N +Rat M)) U }
        [anywhere]

    rule
        { (X |-> 0 => .) U }
        [anywhere]

endmodule

//@ Static semantics of Ursa that does constraint generation for unit analysis.
module URSA-SEMANTICS
    imports URSA-SYNTAX
    imports URSA-UNITS

    configuration
        <T>
            <k color="LightGreen"> $PGM:Stmts </k>
            <uenv color="LightSlateBlue"> .Map </uenv>
            <constraints color="LightSkyBlue"> .Map </constraints>
            <fresh> 0 </fresh>
        </T>


    rule
        S:Stmt Ss:Stmts => S ~> Ss

    rule
        <k> Ty:Type X, Xs; => Ty X; Ty Xs; ...</k>

    rule // special case for real x = 3.14{u};
        <k> Ty:Type X:Id = Z:Float {U}; => Ty X{U}; ...</k>

    rule // special case for real x{u} = 3.14;
        <k> Ty:Type X{U} = Z:Float; => Ty X{U}; ...</k>

    rule
        <k> Ty:Type X:Id = Exp; => Ty X; X = Exp; ...</k>

    rule
        <k> Ty:Type X{U} = Exp; => Ty X{U}; X = Exp; ...</k>

    rule
        <k> Ty:Type X{U}; => . ...</k>
        <uenv>... . => X |-> unit(U) ...</uenv>

    rule
        <k> Ty:Type X; => . ...</k>
        <uenv>... . => X |-> unit(` X) ...</uenv>

    rule
        <k> E:Exp; => E ...</k>

    //@ Constraint generation
    syntax KResult ::= Unit

    rule
        <k> X:Id => U ...</k>
        <uenv>... X |-> U ...</uenv>

    rule
        <k> Z:Float => unit(? I) ...</k>
        <uenv>... . => Z |-> unit(? I) ...</uenv>
        <fresh> I => I +Int 1 </fresh>

    rule
        <k> Z:Float {U} => unit(U) ...</k>
        <uenv>... . => Z |-> unit(U) ...</uenv>

    rule
        <k> U1:KResult + U2:KResult => U1 ...</k>
        <constraints>... . => U1 |-> U2 ...</constraints>

    rule
        <k> U1:KResult - U2:KResult => U1 ...</k>
        <constraints>... . => U1 |-> U2 ...</constraints>

    rule
        <k> U1:KResult * U2:KResult => U1 *u U2 ...</k>

    rule
        <k> (U1:KResult / U2:KResult):Exp => U1 /u U2 ...</k>

    rule
        <k> (U:KResult ^ (N:Int)):Exp => U ^u N ...</k>

    rule
        <k> U:KResult ^ (N / M) => U ^u (N % M) ...</k>

    rule
        <k> X:Id = U2; => . ...</k>
        <uenv>... X |-> U1 ...</uenv>
        <constraints>... . => U1 |-> U2 ...</constraints>

    //@ Constraint simplification rules
    rule
        <constraints>... U |-> U => . ...</constraints>

    rule
        <constraints>... (U1 |-> U2)  (U1 |-> U2 => .) ...</constraints>

endmodule

module URSA
    imports URSA-SYNTAX
    imports URSA-SEMANTICS

endmodule

// Rationals are not built-in yet.
module RATIONALS

    syntax Rat
      ::= Int
        | Int "%" Int

    rule X % X => 1 [anywhere]
    rule X % Y => -1 when X ==Int (Y *Int -1) [anywhere]

    syntax Rat ::= Rat "*Rat" Rat [function]

    rule X:Int *Rat Y:Int => X *Int Y [anywhere]
    rule A:Int *Rat (X % Y) => (A *Int X) % Y [anywhere]
    rule (A % B) *Rat (X % Y) => (A *Int X) % (B *Int Y) [anywhere]

    syntax Rat ::= Rat "+Rat" Rat [function]

    rule X:Int +Rat Y:Int => X +Int Y [anywhere]
    rule A:Int +Rat (X % Y) => (A *Int Y +Int X) % Y [anywhere]
    rule (A % B) +Rat (X % Y) => (A *Int Y +Int B *Int X) % (B *Int Y) [anywhere]

endmodule
