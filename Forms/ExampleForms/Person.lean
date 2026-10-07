import Forms.Domain.Model

namespace Forms.ExampleForms.Person

abbrev address : Ty := .pair .text .natural

abbrev schema : Ty := .pair .text (.pair .boolean address)

def name : Path schema .text := .left .here

def subscribed : Path schema .boolean := .right (.left .here)

def street : Path schema .text := .right (.right (.left .here))

def number : Path schema .natural := .right (.right (.right .here))

def initial : Ty.denote schema := ("Ada", (false, ("Lambda Lane", 12)))

def form : Form schema schema :=
  .group "Person"
    (.field "Name" .text)
    (.group "Newsletter"
      (.field "Subscribed" .checkbox)
      (.visibleWhen (.project subscribed)
        (.group "Address"
          (.field "Street" .text)
          (.field "Number" .natural))))

end Forms.ExampleForms.Person
