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
    pub enum Datalog[v] {
        case Datalog(Array[Constraint[v]], Array[Constraint[v]])
    }

    instance ToString[Datalog[v]] with [v : ToString] {
        pub def toString(cs: Datalog[v]): String =
            let toString = match Datalog(facts, rules) -> {
                let sb = StringBuilder.new();
                Array.append(facts, rules) |>
                Array.map(ToString.toString) |>
                StringBuilder.appendLines!(sb);
                StringBuilder.toString(sb)
            };
            toString(cs) as & Pure
    }
}