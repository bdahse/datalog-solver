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
    pub enum BoolExp[v] {
        case Empty(RelSym)
        case MemberOf(List[RamTerm[v]], RelSym)
        case Eq(RamTerm[v], RamTerm[v])
        case Not(BoolExp[v])
        case And(BoolExp[v], BoolExp[v])
    }

    instance ToString[BoolExp[v]] with [v : ToString] {
        def toString(exp: BoolExp[v]): String = match exp {
            case Empty(relSym) => "${relSym} = ∅"
            case MemberOf(terms, relSym) =>
                let tuple = List.map(ToString.toString, terms) |> String.intercalate(", ");
                "(${tuple}) ∈ ${relSym}"
            case Eq(lhs, rhs) => "${lhs} = ${rhs}"
            case Not(MemberOf(terms, relSym)) =>
                let tuple = List.map(ToString.toString, terms) |> String.intercalate(", ");
                "(${tuple}) ∉ ${relSym}"
            case Not(e) => "not(${e})"
            case And(lhs, rhs) => "${lhs} and ${rhs}"
        }
    }
}