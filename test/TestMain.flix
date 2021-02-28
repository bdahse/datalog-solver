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

use Fixpoint/Ast.{Constraint, HeadTerm, BodyTerm};
use Fixpoint/Ast.Constraint.Constraint;
use Fixpoint/Ast.HeadPredicate.HeadAtom;
use Fixpoint/Ast.BodyPredicate.BodyAtom;
use Fixpoint/Ast.Polarity.{Positive, Negative};
use Fixpoint/Ast.SourceLocation.Unknown;
use Fixpoint/Ast.PredSym.PredSym;
use Fixpoint/Ast.VarSym.VarSym;
use Fixpoint.{compile, interpret};
use ToString.toString;

pub def prog01(): List[Constraint[String]] =
    /// Rich("Magnus").
    /// Age(34).
    /// Rich("Joakim").
    /// Famous("Joakim").
    /// Happy(person) :- Rich(person), Famous(person).
    let fact1 = Constraint(HeadAtom(PredSym("Rich", Unknown),
                                    HeadTerm.Lit("Magnus", Unknown) :: Nil, Unknown),
                            Nil, Unknown);
    let fact2 = Constraint(HeadAtom(PredSym("Age", Unknown),
                                    HeadTerm.Lit("34", Unknown) :: Nil, Unknown),
                            Nil, Unknown);
    let fact3 = Constraint(HeadAtom(PredSym("Rich", Unknown),
                                    HeadTerm.Lit("Joakim", Unknown) :: Nil, Unknown),
                            Nil, Unknown);
    let fact4 = Constraint(HeadAtom(PredSym("Famous", Unknown),
                                    HeadTerm.Lit("Joakim", Unknown) :: Nil, Unknown),
                            Nil, Unknown);
    let rule1 = Constraint(HeadAtom(PredSym("Happy", Unknown),
                                    HeadTerm.Var(VarSym("person", Unknown), Unknown) :: Nil,
                                    Unknown),
                            BodyAtom(PredSym("Rich", Unknown),
                                    Positive,
                                    BodyTerm.Var(VarSym("person", Unknown), Unknown) :: Nil,
                                    Unknown) ::
                            BodyAtom(PredSym("Famous", Unknown),
                                    Positive,
                                    BodyTerm.Var(VarSym("person", Unknown), Unknown) :: Nil,
                                    Unknown) :: Nil,
                            Unknown);
    fact1 :: fact2 :: fact3 :: fact4 :: rule1 :: Nil

pub def prog02(): List[Constraint[String]] =
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
                                    HeadTerm.Lit("A", Unknown) ::
                                    HeadTerm.Lit("B", Unknown) :: Nil, Unknown),
                            Nil, Unknown);
    let fact2 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    HeadTerm.Lit("B", Unknown) ::
                                    HeadTerm.Lit("C", Unknown) :: Nil, Unknown),
                            Nil, Unknown);
    let fact3 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    HeadTerm.Lit("C", Unknown) ::
                                    HeadTerm.Lit("D", Unknown) :: Nil, Unknown),
                            Nil, Unknown);
    let fact4 = Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    HeadTerm.Lit("D", Unknown) ::
                                    HeadTerm.Lit("B", Unknown) :: Nil, Unknown),
                            Nil, Unknown);
    let rule1 = Constraint(HeadAtom(PredSym("Vertex", Unknown),
                                    HeadTerm.Var(VarSym("x", Unknown), Unknown) :: Nil,
                                    Unknown),
                            BodyAtom(PredSym("Edge", Unknown),
                                    Positive,
                                    BodyTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("_", Unknown), Unknown) :: Nil,
                                    Unknown) :: Nil,
                            Unknown);
    let rule2 = Constraint(HeadAtom(PredSym("Vertex", Unknown),
                                    HeadTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown),
                            BodyAtom(PredSym("Edge", Unknown),
                                    Positive,
                                    BodyTerm.Var(VarSym("_", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown) :: Nil,
                            Unknown);
    let rule3 = Constraint(HeadAtom(PredSym("Path", Unknown),
                                    HeadTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    HeadTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown),
                            BodyAtom(PredSym("Edge", Unknown),
                                    Positive,
                                    BodyTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown) :: Nil,
                            Unknown);
    let rule4 = Constraint(HeadAtom(PredSym("Path", Unknown),
                                    HeadTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    HeadTerm.Var(VarSym("z", Unknown), Unknown) :: Nil,
                                    Unknown),
                            BodyAtom(PredSym("Path", Unknown),
                                    Positive,
                                    BodyTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown) ::
                            BodyAtom(PredSym("Edge", Unknown),
                                    Positive,
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("z", Unknown), Unknown) :: Nil,
                                    Unknown) :: Nil,
                            Unknown);
    let rule5 = Constraint(HeadAtom(PredSym("Unconnected", Unknown),
                                    HeadTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    HeadTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown),
                            BodyAtom(PredSym("Vertex", Unknown),
                                    Positive,
                                    BodyTerm.Var(VarSym("x", Unknown), Unknown) :: Nil,
                                    Unknown) ::
                            BodyAtom(PredSym("Vertex", Unknown),
                                    Positive,
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown) ::
                            BodyAtom(PredSym("Path", Unknown),
                                    Negative,
                                    BodyTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown) :: Nil,
                            Unknown);
    let rule6 = Constraint(HeadAtom(PredSym("AntiSymmetric", Unknown),
                                    HeadTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    HeadTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown),
                            BodyAtom(PredSym("Path", Unknown),
                                    Positive,
                                    BodyTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown) ::
                            BodyAtom(PredSym("Path", Unknown),
                                    Negative,
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("x", Unknown), Unknown) :: Nil,
                                    Unknown) :: Nil,
                            Unknown);
    fact1 :: fact2 :: fact3 :: fact4 :: rule1 :: rule2 :: rule3 :: rule4 :: rule5 :: rule6 :: Nil

@test
pub def test01(): Bool & Impure =
    let strat = Map#{
        PredSym("Happy", Unknown) -> 0
    };
    toString(compile(strat, prog01()) |> interpret) ==
    "Map#{Age -> Set#{34 :: Nil}, Famous -> Set#{Joakim :: Nil}, Happy -> Set#{Joakim :: Nil}, Rich -> Set#{Joakim :: Nil, Magnus :: Nil}}"

@test
pub def test02() : Bool & Impure =
    let strat = Map#{
        PredSym("Vertex", Unknown) -> 0,
        PredSym("Path", Unknown) -> 0,
        PredSym("Unconnected", Unknown) -> 1,
        PredSym("AntiSymmetric", Unknown) -> 1
    };
    toString(compile(strat, prog02()) |> interpret) ==
    "Map#{AntiSymmetric -> Set#{A :: B :: Nil, A :: C :: Nil, A :: D :: Nil}, Edge -> Set#{A :: B :: Nil, B :: C :: Nil, C :: D :: Nil, D :: B :: Nil}, Path -> Set#{A :: B :: Nil, A :: C :: Nil, A :: D :: Nil, B :: B :: Nil, B :: C :: Nil, B :: D :: Nil, C :: B :: Nil, C :: C :: Nil, C :: D :: Nil, D :: B :: Nil, D :: C :: Nil, D :: D :: Nil}, Unconnected -> Set#{A :: A :: Nil, B :: A :: Nil, C :: A :: Nil, D :: A :: Nil}, Vertex -> Set#{A :: Nil, B :: Nil, C :: Nil, D :: Nil}}"