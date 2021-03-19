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

use Fixpoint.{solveWithStratification};
use Fixpoint/Ast.{HeadTerm, BodyTerm, Polarity};
use Fixpoint/Ast.Constraint.Constraint;
use Fixpoint/Ast.Datalog.Datalog;
use Fixpoint/Ast.HeadPredicate.HeadAtom;
use Fixpoint/Ast.BodyPredicate.BodyAtom;
use Fixpoint/Ast.PredSym.PredSym;
use Fixpoint/Ast.VarSym.VarSym;
use Fixpoint/Ast.SourceLocation.Unknown;

rel Edge(x: Int32, y: Int32)
rel Path(x: Int32, y: Int32)

@benchmark
pub def benchmarkFlix(): Bool =
    let facts =
        List.range(0, 250) |>
        List.foldLeft((acc: #{ Edge, Path }, s: Int) -> {
            acc <+> Edge(s, (s + 1) % 250).
        }, #{});
    let rules = #{
        Path(x, y) :- Edge(x, y).
        Path(x, z) :- Path(x, y), Edge(y, z).
    };
    (solve facts <+> rules) |= Path(1, 20).

pub def benchmark(): Unit & Impure =
    let facts = Array.init(i -> {
        Constraint(HeadAtom(PredSym("Edge", Unknown),
                            [HeadTerm.Lit(i, Unknown),
                             HeadTerm.Lit((i+1) % 250, Unknown)], Unknown),
                    [], Unknown)
    }, 250);
    let rule1 = Constraint(HeadAtom(PredSym("Path", Unknown),
                                    [HeadTerm.Var(VarSym("x", Unknown), Unknown),
                                     HeadTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Edge", Unknown),
                                    Polarity.Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    let rule2 = Constraint(HeadAtom(PredSym("Path", Unknown),
                                    [HeadTerm.Var(VarSym("x", Unknown), Unknown),
                                     HeadTerm.Var(VarSym("z", Unknown), Unknown)],
                                    Unknown),
                            [BodyAtom(PredSym("Edge", Unknown),
                                    Polarity.Positive,
                                    [BodyTerm.Var(VarSym("x", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("y", Unknown), Unknown)],
                                    Unknown),
                            BodyAtom(PredSym("Path", Unknown),
                                    Polarity.Positive,
                                    [BodyTerm.Var(VarSym("y", Unknown), Unknown),
                                     BodyTerm.Var(VarSym("z", Unknown), Unknown)],
                                    Unknown)],
                            Unknown);
    let db = Map#{PredSym("Path", Unknown) -> 0} |> solveWithStratification(Datalog(facts, [rule1, rule2]));
    println(db)

def main(_args: Array[String]): Int32 & Impure =
    benchmark();
    0
