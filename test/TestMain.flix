/*
 * Copyright 2021 Benjamin Dahse
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use Fixpoint/Ast.{ConstraintSystem, Constraint, HeadTerm, BodyTerm};
use Fixpoint/Ast.ConstraintSystem.ConstraintSystem;
use Fixpoint/Ast.Constraint.Constraint;
use Fixpoint/Ast.HeadPredicate.HeadAtom;
use Fixpoint/Ast.BodyPredicate.{BodyAtom, GuardAtom};
use Fixpoint/Ast.Polarity.{Positive, Negative};
use Fixpoint/Ast.SourceLocation.Unknown;
use Fixpoint/Ast.PredSym.PredSym;
use Fixpoint/Ast.VarSym.VarSym;
use Fixpoint.{compile, interpret, hoistStmt, queryStmt, lowerStmt};
use ToString.toString;

@test
pub def test01(): Bool & Impure =
    /// Rich("Magnus").
    /// Age(34).
    /// Rich("Joakim").
    /// Famous("Joakim").
    /// Happy(person) :- Rich(person), Famous(person).
    let fact1 = Constraint(HeadAtom(PredSym("Rich", Unknown),
                                    [HeadTerm.Lit("Magnus", Unknown)], Unknown),
                            [], Unknown);
    let fact2 = Constraint(HeadAtom(PredSym("Age", Unknown),
                                    [HeadTerm.Lit("34", Unknown)], Unknown),
                            [], Unknown);
    let fact3 = Constraint(HeadAtom(PredSym("Rich", Unknown),
                                    [HeadTerm.Lit("Joakim", Unknown)], Unknown),
                            [], Unknown);
    let fact4 = Constraint(HeadAtom(PredSym("Famous", Unknown),
                                    [HeadTerm.Lit("Joakim", Unknown)], Unknown),
                            [], Unknown);
    let rule1 = Constraint(HeadAtom(PredSym("Happy", Unknown),
                                    [HeadTerm.Var(VarSym("person", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Rich", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("person", Unknown), Unknown)],
                                    Unknown),
                            BodyAtom(PredSym("Famous", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("person", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    Map#{PredSym("Happy", Unknown) -> 0} |>
    compile(ConstraintSystem([fact1, fact2, fact3, fact4], [rule1])) |>
    hoistStmt |>
    queryStmt |>
    lowerStmt |>
    interpret |>
    toString == "Model#{Age#{34}, Famous#{Joakim}, Happy#{Joakim}, Rich#{Magnus, Joakim}}"

@test
pub def test02() : Bool & Impure =
    /// Edge(A, B).
    /// Edge(B, C).
    /// Edge(C, D).
    /// Edge(D, B).
    /// Vertex(x) :- Edge(x, _).
    /// Vertex(y) :- Edge(_, y).
    /// Path(x, y) :- Edge(x, y).
    /// Path(x, z) :- Path(x, y), Edge(y, z).
    /// Unconnected(x, y) :- Vertex(x), Vertex(y), not Path(x, y).
    /// AntiSymmetric(x, y) :- Path(x, y), not Path(y, x).
    let fact1 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    [HeadTerm.Lit("A", Unknown),
                                     HeadTerm.Lit("B", Unknown)], Unknown),
                            [], Unknown);
    let fact2 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    [HeadTerm.Lit("B", Unknown),
                                     HeadTerm.Lit("C", Unknown)], Unknown),
                            [], Unknown);
    let fact3 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    [HeadTerm.Lit("C", Unknown),
                                     HeadTerm.Lit("D", Unknown)], Unknown),
                            [], Unknown);
    let fact4 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    [HeadTerm.Lit("D", Unknown),
                                     HeadTerm.Lit("B", Unknown)], Unknown),
                            [], Unknown);
    let rule1 = Constraint(HeadAtom(PredSym("Vertex", Unknown),
                                    [HeadTerm.Var(VarSym("x", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Edge", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("_", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    let rule2 = Constraint(HeadAtom(PredSym("Vertex", Unknown),
                                    [HeadTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Edge", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("_", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    let rule3 = Constraint(HeadAtom(PredSym("Path", Unknown),
                                    [HeadTerm.Var(VarSym("x", Unknown), Unknown),
                                     HeadTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Edge", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    let rule4 = Constraint(HeadAtom(PredSym("Path", Unknown),
                                    [HeadTerm.Var(VarSym("x", Unknown), Unknown),
                                     HeadTerm.Var(VarSym("z", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Path", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            BodyAtom(PredSym("Edge", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("y", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("z", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    let rule5 = Constraint(HeadAtom(PredSym("Unconnected", Unknown),
                                    [HeadTerm.Var(VarSym("x", Unknown), Unknown),
                                     HeadTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Vertex", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown)],
                                    Unknown),
                            BodyAtom(PredSym("Vertex", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            BodyAtom(PredSym("Path", Unknown),
                                    Negative,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    let rule6 = Constraint(HeadAtom(PredSym("AntiSymmetric", Unknown),
                                    [HeadTerm.Var(VarSym("x", Unknown), Unknown),
                                     HeadTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Path", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            BodyAtom(PredSym("Path", Unknown),
                                    Negative,
                                    [BodyTerm.Var(VarSym("y", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("x", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    Map#{
        PredSym("Vertex", Unknown) -> 0,
        PredSym("Path", Unknown) -> 0,
        PredSym("Unconnected", Unknown) -> 1,
        PredSym("AntiSymmetric", Unknown) -> 1
    } |>
    compile(ConstraintSystem([fact1, fact2, fact3, fact4], [rule1, rule2, rule3, rule4, rule5, rule6])) |>
    hoistStmt |>
    queryStmt |>
    lowerStmt |>
    interpret |>
    toString == "Model#{AntiSymmetric#{(A, D), (A, C), (A, B)}, Edge#{(D, B), (C, D), (B, C), (A, B)}, Path#{(D, D), (D, C), (D, B), (C, D), (C, C), (C, B), (B, D), (B, C), (B, B), (A, D), (A, C), (A, B)}, Unconnected#{(D, A), (C, A), (B, A), (A, A)}, Vertex#{D, C, B, A}}"

@test
pub def test03(): Bool & Impure =
    /// Number(2).
    /// Number(3).
    /// Number(5).
    /// Number(7).
    /// Sum(f(x, 0)) :- Number(x).
    /// Sum(f(x, y)) :- Number(x), Number(y).
    let f = args -> match args {
        case [x, y] => "${x} + ${y}"
        case _ => "0"
    };
    let fact1 = Constraint(HeadAtom(PredSym("Number", Unknown),
                                    [HeadTerm.Lit("2", Unknown)], Unknown),
                            [], Unknown);
    let fact2 = Constraint(HeadAtom(PredSym("Number", Unknown),
                                    [HeadTerm.Lit("3", Unknown)], Unknown),
                            [], Unknown);
    let fact3 = Constraint(HeadAtom(PredSym("Number", Unknown),
                                    [HeadTerm.Lit("5", Unknown)], Unknown),
                            [], Unknown);
    let fact4 = Constraint(HeadAtom(PredSym("Number", Unknown),
                                    [HeadTerm.Lit("7", Unknown)], Unknown),
                            [], Unknown);
    let rule1 = Constraint(HeadAtom(PredSym("Sum", Unknown),
                                    [HeadTerm.App(f,
                                                [HeadTerm.Var(VarSym("x", Unknown), Unknown),
                                                HeadTerm.Lit("0", Unknown)],
                                                Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Number", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    let rule2 = Constraint(HeadAtom(PredSym("Sum", Unknown),
                                    [HeadTerm.App(f,
                                                [HeadTerm.Var(VarSym("x", Unknown), Unknown),
                                                 HeadTerm.Var(VarSym("y", Unknown), Unknown)],
                                                Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Number", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown)],
                                    Unknown),
                            BodyAtom(PredSym("Number", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    Map#{PredSym("Sum", Unknown) -> 0} |>
    compile(ConstraintSystem([fact1, fact2, fact3, fact4], [rule1, rule2])) |>
    hoistStmt |>
    queryStmt |>
    lowerStmt |>
    interpret |>
    toString == "Model#{Number#{7, 5, 3, 2}, Sum#{7 + 7, 7 + 5, 7 + 3, 7 + 2, 7 + 0, 5 + 7, 5 + 5, 5 + 3, 5 + 2, 5 + 0, 3 + 7, 3 + 5, 3 + 3, 3 + 2, 3 + 0, 2 + 7, 2 + 5, 2 + 3, 2 + 2, 2 + 0}}"

@test
pub def test04(): Bool & Impure =
    /// Edge(A, 80, B).
    /// Edge(B, 70, C).
    /// Edge(C, 110, D).
    /// Edge(D, 50. B).
    /// Path(x, y) :- Edge(x, speedLimit, y), if speedLimit >= 70.
    /// Path(x, z) :- Path(x, y), Edge(y, speedLimit, z), if speedLimit >= 70.
    let f = args -> match args {
        case [x] => x >= "070"
        case _ => false
    };
    let fact1 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    [HeadTerm.Lit("A", Unknown),
                                     HeadTerm.Lit("080", Unknown),
                                     HeadTerm.Lit("B", Unknown)], Unknown),
                            [], Unknown);
    let fact2 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    [HeadTerm.Lit("B", Unknown),
                                     HeadTerm.Lit("070", Unknown),
                                     HeadTerm.Lit("C", Unknown)], Unknown),
                            [], Unknown);
    let fact3 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    [HeadTerm.Lit("C", Unknown),
                                     HeadTerm.Lit("110", Unknown),
                                     HeadTerm.Lit("D", Unknown)], Unknown),
                            [], Unknown);
    let fact4 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    [HeadTerm.Lit("D", Unknown),
                                     HeadTerm.Lit("050", Unknown),
                                     HeadTerm.Lit("B", Unknown)], Unknown),
                            [], Unknown);
    let rule1 = Constraint(HeadAtom(PredSym("Path", Unknown),
                                    [HeadTerm.Var(VarSym("x", Unknown), Unknown),
                                     HeadTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Edge", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("speedLimit", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            GuardAtom(f,
                                    [BodyTerm.Var(VarSym("speedLimit", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    let rule2 = Constraint(HeadAtom(PredSym("Path", Unknown),
                                    [HeadTerm.Var(VarSym("x", Unknown), Unknown),
                                     HeadTerm.Var(VarSym("z", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Path", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            BodyAtom(PredSym("Edge", Unknown),
                                    Positive,
                                    [BodyTerm.Var(VarSym("y", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("speedLimit", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("z", Unknown), Unknown)],
                                    Unknown),
                            GuardAtom(f,
                                    [BodyTerm.Var(VarSym("speedLimit", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    Map#{PredSym("Path", Unknown) -> 0} |>
    compile(ConstraintSystem([fact1, fact2, fact3, fact4], [rule1, rule2])) |>
    hoistStmt |>
    queryStmt |>
    lowerStmt |>
    interpret |>
    toString == "Model#{Edge#{(D, 050, B), (C, 110, D), (B, 070, C), (A, 080, B)}, Path#{(C, D), (B, D), (B, C), (A, D), (A, C), (A, B)}}"
