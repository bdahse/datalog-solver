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

namespace Fixpoint/Ram {
    pub enum RelOp[v] {
        case Search(RowVar, RelSym, List[BoolExp[v]], RelOp[v])
        case Query(RowVar, RelSym, List[RamTerm[v]], List[BoolExp[v]], RelOp[v])
        case Project(List[RamTerm[v]], RelSym)
    }

    instance ToString[RelOp[v]] with [v : ToString] {
        def toString(op: RelOp[v]): String =
            let nl = String.lineSeparator();
            match op {
                case Search(var, relSym, Nil, body) =>
                    "search ${var} ∈ ${relSym} do${nl}${String.indent(4, "${body}")}end"
                case Search(var, relSym, where, body) =>
                    let where = List.map(ToString.toString, where) |> String.intercalate(" Λ ");
                    "search ${var} ∈ ${relSym} where${nl}${String.indent(4, "${where}")}do${nl}${String.indent(4, "${body}")}end"
                case Query(var, relSym, rangeQuery, Nil, body) =>
                    let query =
                        List.mapWithIndex(term -> i -> {
                            ToString.toString(BoolExp.Eq(RamTerm.Attribute(var, i), term))
                        }, rangeQuery) |>
                        String.intercalate(" ∧ ");
                    "query {${var} ∈ ${relSym} | ${query}} do${nl}${String.indent(4, "${body}")}end"
                case Query(var, relSym, rangeQuery, where, body) =>
                    let where = List.map(ToString.toString, where) |> String.intercalate(" Λ ");
                    let query =
                        List.mapWithIndex(term -> i -> {
                            ToString.toString(BoolExp.Eq(RamTerm.Attribute(var, i), term))
                        }, rangeQuery) |>
                        String.intercalate(" ∧ ");
                    "query {${var} ∈ ${relSym} | ${query}} where${nl}${String.indent(4, "${where}")}do${nl}${String.indent(4, "${body}")}end"
                case Project(terms, relSym) =>
                    let tuple = List.map(ToString.toString, terms) |> String.intercalate(", ");
                    "project (${tuple}) into ${relSym}"
            }
    }
}