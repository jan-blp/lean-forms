module

public import Forms

open Forms.Model Forms.Model.Sugar

namespace Tests.Sugar

-- Exposed public declarations must infer the index before elaborating the pane lookup.
@[expose] public def tabInference : Component [] String := named%
  present%
    tabs% active, bar := "View", #v["Edit", "Preview"];
    own% edit := .field .self "Text" .text;
    own% preview := .computed "Preview" { inputs := inputs[path[]], run := id };
    .arrange {
      inputs := inputs[.ui ref[active]]
      run := fun active => .group none [
        .place slot[bar],
        #v[.place slot[edit], .place slot[preview]][active]] }

example : tabInference =
    (Component.present <|
      .tabs "View" (.const #v["Edit", "Preview"]) <|
        .own (.field .self "Text" .text) <|
          .own (.computed "Preview" { inputs := inputs[path[]], run := id }) <|
            .arrange {
              inputs := inputs[.ui (.there (.there (.there .here)))]
              run := fun (active : Fin 2) => .group none [
                .place (.there (.there .here)),
                #v[.place (.there .here), .place .here][active]] }) := rfl

end Tests.Sugar
