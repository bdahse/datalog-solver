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
    pub enum RelSym {
        case Full(String)
        case Delta(String)
        case New(String)
    }

    instance ToString[RelSym] {
        def toString(relSym: RelSym): String = match relSym {
            case Full(name) => name
            case Delta(name) => "Δ${name}"
            case New(name) => "Δ${name}'"
        }
    }

    instance Order[RelSym] {
        def less(a: RelSym, b: RelSym): Bool = match a <=> b {
            case LessThan => true
            case _ => false
        }

        def lessEqual(a: RelSym, b: RelSym): Bool = match a <=> b {
            case LessThan => true
            case EqualTo => true
            case _ => false
        }

        def greater(a: RelSym, b: RelSym): Bool = match a <=> b {
            case GreaterThan => true
            case _ => false
        }

        def greaterEqual(a: RelSym, b: RelSym): Bool = match a <=> b {
            case GreaterThan => true
            case EqualTo => true
            case _ => false
        }

        def compare(a: RelSym, b: RelSym): Comparison = match (a, b) {
            case (Full(s1), Full(s2))   => s1 <=> s2
            case (Delta(s1), Delta(s2)) => s1 <=> s2
            case (New(s1), New(s2))     => s1 <=> s2
            case (Full(_), _) => GreaterThan
            case (_, Full(_)) => LessThan
            case (Delta(_), New(_)) => GreaterThan
            case (New(_), Delta(_)) => LessThan
        }
    }
}