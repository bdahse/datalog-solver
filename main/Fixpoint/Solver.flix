/*
 * Copyright 2021 Magnus Madsen
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

namespace Fixpoint {

    namespace Ast {

        pub enum Constraint {
            case Constraint(List[ConstraintParam], HeadPredicate, List[BodyPredicate], SourceLocation)
        }

        pub enum ConstraintParam {
            case HeadParam(VarSym, SourceLocation),
            case RuleParam(VarSym, SourceLocation)
        }

        pub enum HeadPredicate {
            case HeadAtom(PredSym, List[HeadTerm], SourceLocation)
        }

        pub enum BodyPredicate {
            case BodyAtom(PredSym, List[BodyTerm])
        }

        pub enum HeadTerm {
            case HeadQuantVar(VarSym, SourceLocation),
            case HeadCapturedVar(VarSym, SourceLocation),
            case HeadLit(String, SourceLocation)
        }

        pub enum BodyTerm {
            case BodyQuantVar(VarSym, SourceLocation),
            case BodyCapturedVar(VarSym, SourceLocation),
            case BodyLit(String, SourceLocation)
        }

        pub enum PredSym {
            case PredSym(String, SourceLocation)
        }

        pub enum VarSym {
            case VarSym(String, SourceLocation)
        }

        pub enum SourceLocation {
            case Unknown,
            case SourceLocation(String, Int32, Int32) // Filename and char interval
        }

        pub def foo() : List[Constraint] =
            let fact1 = Constraint(Nil, HeadAtom(PredSym("Rich", Unknown),
                                                 HeadLit("Magnus", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let fact2 = Constraint(Nil, HeadAtom(PredSym("Age", Unknown),
                                                 HeadLit("34", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let fact3 = Constraint(Nil, HeadAtom(PredSym("Rich", Unknown),
                                                 HeadLit("Joakim", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let fact4 = Constraint(Nil, HeadAtom(PredSym("Famous", Unknown),
                                                 HeadLit("Joakim", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let rule1 = Constraint(HeadParam(VarSym("person", Unknown), Unknown) :: Nil,
                                   HeadAtom(PredSym("Happy", Unknown),
                                            HeadQuantVar(VarSym("person", Unknown), Unknown) :: Nil,
                                            Unknown),
                                    BodyAtom(PredSym("Rich", Unknown),
                                             BodyQuantVar(VarSym("person", Unknown), Unknown) :: Nil) ::
                                             BodyAtom(PredSym("Famous", Unknown),
                                                      BodyQuantVar(VarSym("person", Unknown), Unknown) :: Nil) :: Nil,
                                   Unknown);
            fact1 :: fact2 :: fact3 :: fact4 :: rule1 :: Nil
    }

    namespace RelationalAlgebraMachine {

        // TODO

    }

}
/// Rich("Magnus").
/// Age(34).
/// Rich("Joakim").
/// Famous("Joakim").
/// Happy(person) :- Rich(person), Famous(person).