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

use Fixpoint.{compile, interpret, hoistStmt, queryStmt};
use Fixpoint.Model.Model;
use Fixpoint/Ast.{HeadTerm, BodyTerm, Polarity};
use Fixpoint/Ast.Constraint.Constraint;
use Fixpoint/Ast.HeadPredicate.HeadAtom;
use Fixpoint/Ast.BodyPredicate.BodyAtom;
use Fixpoint/Ast.PredSym.PredSym;
use Fixpoint/Ast.VarSym.VarSym;
use Fixpoint/Ast.SourceLocation.Unknown;

pub def benchmark(): Unit & Impure =
    let rand = Random.nextNatWithMax(Random.new());
    let facts =
        List.unfold(i -> if (i < 1000) {
            let fact =
                Constraint(HeadAtom(PredSym("Edge", Unknown),
                                    HeadTerm.Lit(ToString.toString(rand(1000)), Unknown) ::
                                    HeadTerm.Lit(ToString.toString(rand(1000)), Unknown) :: Nil, Unknown),
                            Nil, Unknown);
            Some((fact, i+1))
        } else {
            None
        }, 0);
    let rule1 = Constraint(HeadAtom(PredSym("Path", Unknown),
                                    HeadTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    HeadTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown),
                            BodyAtom(PredSym("Edge", Unknown),
                                    Polarity.Positive,
                                    BodyTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown) :: Nil,
                            Unknown);
    let rule2 = Constraint(HeadAtom(PredSym("Path", Unknown),
                                    HeadTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    HeadTerm.Var(VarSym("z", Unknown), Unknown) :: Nil,
                                    Unknown),
                            BodyAtom(PredSym("Path", Unknown),
                                    Polarity.Positive,
                                    BodyTerm.Var(VarSym("x", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                    Unknown) ::
                            BodyAtom(PredSym("Edge", Unknown),
                                    Polarity.Positive,
                                    BodyTerm.Var(VarSym("y", Unknown), Unknown) ::
                                    BodyTerm.Var(VarSym("z", Unknown), Unknown) :: Nil,
                                    Unknown) :: Nil,
                            Unknown);
    let Model(db) =
        Map#{PredSym("Path", Unknown) -> 0} |>
        compile(rule1 :: rule2 :: facts) |>
        hoistStmt |>
        queryStmt |>
        interpret;
    let path = Map.getWithDefault("Path", Set#{}, db);
    println("Deduced ${Set.size(path)} facts.")

def main(_args: Array[String]): Int32 & Impure =
    benchmark();
    0
