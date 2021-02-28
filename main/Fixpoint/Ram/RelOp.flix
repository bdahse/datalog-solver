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
        case Search(RowVar, RelSym, Option[BoolExp[v]], RelOp[v])
        case Project(List[RamTerm[v]], RelSym)
    }

    instance ToString[RelOp[v]] with [v : ToString] {
        def toString(op: RelOp[v]): String =
            use ToString.toString;
            let nl = String.lineSeparator();
            match op {
                case Search(var, relSym, Some(cond), body) =>
                    "search " + toString(var) + " ∈ " + toString(relSym) + " where" + nl +
                        String.indent(4, toString(cond)) +
                    "do" + nl +
                        String.indent(4, toString(body)) +
                    "end"
                case Search(var, relSym, None, body) =>
                    "search " + toString(var) + " ∈ " + toString(relSym) + " do" + nl +
                        String.indent(4, toString(body)) +
                    "end"
                case Project(terms, relSym) =>
                    let tuple = List.map(toString, terms) |> String.intercalate(", ");
                    "project (" + tuple + ") into " + toString(relSym)
            }
    }
}