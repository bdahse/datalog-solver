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
namespace Fixpoint/Ast {
    pub enum HeadTerm[v] {
        case Var(VarSym, SourceLocation)
        case Lit(v, SourceLocation)
        case App(v -> v, HeadTerm[v], SourceLocation)
    }

    instance ToString[HeadTerm[v]] with [v : ToString] {
        def toString(term: HeadTerm[v]): String = match term {
            case HeadTerm.Var(varSym, _) => ToString.toString(varSym)
            case HeadTerm.Lit(v, _) => ToString.toString(v)
            case HeadTerm.App(_, t, _) => "f(${t})"
        }
    }
}