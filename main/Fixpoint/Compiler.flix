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

use Fixpoint/Ast.Constraint;
use Fixpoint/Ast.Constraint.Constraint;
use Fixpoint/Ast.PredSym;
use Fixpoint/Ast.PredSym.PredSym;
use Fixpoint/Ast.HeadPredicate.HeadAtom;
use Fixpoint/Ast.HeadTerm;
use Fixpoint/Ram.{Stmt, RelOp, RelSym, RamTerm};

namespace Fixpoint {
    def _compile(cs: List[Constraint[v]]): Stmt[v] =
        let facts = compileFacts(cs);
        List.fold(facts :: Nil)

    def compileFacts(cs: List[Constraint[v]]): Stmt[v] =
        let toRam = term -> match term {
            case HeadTerm.Var(_, _) => ??? // Impossible
            case HeadTerm.Lit(v, _) => RamTerm.Lit(v)
            case HeadTerm.App(_, _, _) => ??? // TODO: how to handle this?
        };
        let compile = fact -> match fact {
            case Constraint(_, HeadAtom(PredSym(sym, _), terms, _), _, _) =>
                Stmt.Insert(RelOp.Project(List.map(toRam, terms), RelSym.Full(sym)))
        };
        List.map(compile, cs.facts()) |> List.fold

    def facts(cs: List[Constraint[v]]): List[Constraint[v]] =
        let isFact = c -> match c {
            case Constraint(Nil, _, Nil, _) => true
            case _ => false
        };
        List.filter(isFact, cs)
}