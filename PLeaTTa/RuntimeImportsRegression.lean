import PLeaTTa.RuntimeImports

namespace PLeaTTa.RuntimeImportsRegression

open Metta (Atom)

private def bang (items : List Atom) : Atom :=
  .expr [.sym "!", .expr items]

#guard (unsupportedRuntimeDirective?
  (bang [.sym "import_prolog_function", .sym "get_time"])).isNone

#guard (unsupportedRuntimeDirective?
  (bang [.sym "import_prolog_function", .sym "not_registered"])).isSome

#guard (unsupportedRuntimeDirective?
  (bang [.sym "import_prolog_functions_from_file", .sym "skills.pl",
    .expr [.sym "shell", .sym "first_char", .sym "gc"]])).isNone

#guard (unsupportedRuntimeDirective?
  (bang [.sym "import!", .sym "&persistent",
    .expr [.sym "persistentPath"]])).isSome

#guard (unsupportedRuntimeDirective?
  (bang [.sym "export!", .sym "&persistent",
    .expr [.sym "persistentPath"]])).isSome

#guard (unsupportedRuntimeDirective?
  (bang [.sym "import!", .sym "&self", .gnd (.str "module.metta")])).isNone

#guard (unsupportedRuntimeDirective?
  (bang [.sym "py-call", .expr [.sym "math.sqrt", .gnd (.int 4)]])).isNone

#guard (unsupportedRuntimeDirective?
  (.expr [.sym "=", .expr [.sym "sleep", .var "seconds"],
    .expr [.sym "progn",
      .expr [.sym "translatePredicate",
        .expr [.sym "sleep", .var "seconds"]],
      .sym "True"]])).isNone

#guard (unsupportedRuntimeDirective?
  (bang [.sym "translatePredicate",
    .expr [.sym "sleep", .gnd (.int 1)]])).isSome

#guard (compileProgramSequentialForms (fun _ => false)
    [.importBegin, .importEnd true]).toOption.map (fun result => result.2) ==
  some [.importBegin, .importEnd true]

#guard importedPrologHostBacked "shell"
#guard !importedPrologHostBacked "first_char"
#guard !importedPrologHostBacked "gc"

#guard match compileProgramSequentialForms (fun _ => false)
    [.prologRegister ["host_double"] true,
     .atom (bang [.sym "host_double", .gnd (.int 21)]) true] with
  | .ok (_, [.prologRegister ["host_double"] true,
      .query [Goal.bin "translatePredicate" [_] _] _ true]) => true
  | _ => false

end PLeaTTa.RuntimeImportsRegression
