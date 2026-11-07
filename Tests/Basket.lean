module

public import Forms.ExampleForms.Basket
public import Forms.Runtime.CompiledView

public meta import Forms.Core.DataType
public meta import Forms.ExampleForms.Basket

@[expose] public section

namespace Tests.Basket
open Forms Forms.Composition Forms.ExampleForms.Basket

def searchFor (query : String) : ⟦basket⟧ :=
  (Path.field .filters (.field .search .self) : Path basket .text).set query initial

def chooseCategory (c : CategoryFilter) : ⟦basket⟧ :=
  (Path.field .filters (.field .category .self) : Path basket (.enum categoryFilters)).set c initial

def sortWith (s : SortOrder) : ⟦basket⟧ :=
  (Path.field .filters (.field .sort .self) : Path basket (.enum sortOrders)).set s initial

#guard visibleProducts.eval initial == [.backpack, .mug, .notebook, .pen, .bottle]
#guard visibleProducts.eval (searchFor "NOTE") == [.notebook]
#guard visibleProducts.eval (searchFor "missing") == []
#guard visibleProducts.eval (chooseCategory (.only .stationery)) == [.notebook, .pen]
#guard visibleProducts.eval (sortWith .priceLow) == [.pen, .notebook, .mug, .bottle, .backpack]
#guard visibleProducts.eval (sortWith .priceHigh) == [.backpack, .bottle, .mug, .notebook, .pen]
#guard total.eval (searchFor "missing") == 16
#guard total.eval (itemsPath.set [] initial) == 0

def mugSelected : ⟦basket⟧ :=
  (Path.field .selected .self : Path basket product).set .mug initial
#guard selectedItem.eval mugSelected .product == .mug
#guard selectedItem.eval mugSelected .quantity == 1
#guard total.eval (itemsPath.set [line .notebook 2, line .pen 3, line .mug 1] initial) == 28

-- Moving an expression under a larger input must preserve the search query and sorting.
def nested : DataType := .record basketFields fun _ => basket
#guard (Expr.weaken (.field .items .self : Path nested basket) visibleProducts).eval
  (fun _ => searchFor "PEN") == [.pen]

def run : IO Unit := do
  let view := Runtime.CompiledView.render basketView initial
  unless !view.controls.isEmpty do throw (IO.userError "Basket controls missing")
  IO.println "PASS: basket queries, selected item, and compiled view"
end Tests.Basket
