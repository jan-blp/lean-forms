module

public import Forms.Core.Component.Builder

@[expose] public section

namespace Forms.ExampleForms.Basket

open Forms.Composition

inductive Product where
  | notebook
  | pen
  | mug
  | bottle
  | backpack
  deriving DecidableEq, BEq

instance : FinEnum Product :=
  FinEnum.ofList [.notebook, .pen, .mug, .bottle, .backpack] (by grind [Product])

def products : Enum where
  type := Product
  label
    | .notebook => "Notebook"
    | .pen => "Pen"
    | .mug => "Mug"
    | .bottle => "Water bottle"
    | .backpack => "Backpack"

inductive Category where
  | stationery
  | home
  | outdoors
  deriving DecidableEq, BEq

instance : FinEnum Category :=
  FinEnum.ofList [.stationery, .home, .outdoors] (by grind [Category])

def categories : Enum where
  type := Category
  label
    | .stationery => "Stationery"
    | .home => "Home"
    | .outdoors => "Outdoors"

def category : Product → Category
  | .notebook => .stationery
  | .pen => .stationery
  | .mug => .home
  | .bottle => .outdoors
  | .backpack => .outdoors

def price : Product → Nat
  | .notebook => 5
  | .pen => 2
  | .mug => 12
  | .bottle => 18
  | .backpack => 35

abbrev product : DataType := .enum products

def productName : ⟦product⟧ → String := products.label

inductive CategoryFilter where
  | all
  | only (category : Category)
  deriving DecidableEq

instance : FinEnum CategoryFilter :=
  FinEnum.ofList [.all, .only .stationery, .only .home, .only .outdoors]
    (by grind [CategoryFilter, Category])

def categoryFilters : Enum where
  type := CategoryFilter
  label
    | .all => "All categories"
    | .only c => categories.label c
  label_injective := by grind [Function.Injective, categories, Category]

inductive Budget where
  | any
  | ten
  | twenty
  deriving DecidableEq
instance : FinEnum Budget := FinEnum.ofList [.any, .ten, .twenty] (by grind [Budget])
def budgets : Enum where
  type := Budget
  label
    | .any => "Any price"
    | .ten => "Up to EUR 10"
    | .twenty => "Up to EUR 20"

inductive SortOrder where
  | name
  | priceLow
  | priceHigh
  deriving DecidableEq
instance : FinEnum SortOrder :=
  FinEnum.ofList [.name, .priceLow, .priceHigh] (by grind [SortOrder])
def sortOrders : Enum where
  type := SortOrder
  label
    | .name => "Name"
    | .priceLow => "Price: low to high"
    | .priceHigh => "Price: high to low"

inductive FilterField where
  | search
  | category
  | budget
  | sort
  deriving DecidableEq
instance : FinEnum FilterField :=
  FinEnum.ofList [.search, .category, .budget, .sort] (by grind [FilterField])
def filterFields : Enum where
  type := FilterField
  label
    | .search => "search"
    | .category => "category"
    | .budget => "budget"
    | .sort => "sort"
abbrev filters : DataType := .record filterFields fun
  | .search => .text
  | .category => .enum categoryFilters
  | .budget => .enum budgets
  | .sort => .enum sortOrders

inductive ItemField where
  | product
  | quantity
  deriving DecidableEq
instance : FinEnum ItemField := FinEnum.ofList [.product, .quantity] (by grind [ItemField])
def itemFields : Enum where
  type := ItemField
  label
    | .product => "product"
    | .quantity => "quantity"
abbrev item : DataType := .record itemFields fun
  | .product => product
  | .quantity => .natural

def line (p : Product) (quantity : Nat) : ⟦item⟧
  | .product => p
  | .quantity => quantity

def unitPrice (value : ⟦item⟧) : Nat := price (value .product)
def subtotal (value : ⟦item⟧) : Nat := value .quantity * unitPrice value

inductive Page where
  | catalogue
  | basket
  deriving DecidableEq, BEq

instance : FinEnum Page := FinEnum.ofList [.catalogue, .basket] (by grind [Page])
def pages : Enum where
  type := Page
  label
    | .catalogue => "Catalogue"
    | .basket => "Basket"

inductive BasketField where
  | page
  | filters
  | selected
  | items
  deriving DecidableEq
instance : FinEnum BasketField :=
  FinEnum.ofList [.page, .filters, .selected, .items] (by grind [BasketField])
def basketFields : Enum where
  type := BasketField
  label
    | .page => "page"
    | .filters => "filters"
    | .selected => "selected"
    | .items => "items"
abbrev basket : DataType := .record basketFields fun
  | .page => .enum pages
  | .filters => filters
  | .selected => product
  | .items => .list item

def itemsPath : Path basket (.list item) := .field .items .self
def filtersPath : Path basket filters := .field .filters .self

def initial : ⟦basket⟧
  | .page => .catalogue
  | .filters => fun
      | .search => ""
      | .category => .all
      | .budget => .any
      | .sort => .name
  | .selected => .notebook
  | .items => [line .notebook 2, line .pen 3]

def categoryMatches (value : ⟦basket⟧) : List Product :=
  match value .filters .category with
  | .all => FinEnum.toList Product
  | .only c => (FinEnum.toList Product).filter fun p => category p == c

def affordable (value : ⟦basket⟧) : List Product :=
  match value .filters .budget with
  | .any => categoryMatches value
  | .ten => (categoryMatches value).filter fun p => price p ≤ 10
  | .twenty => (categoryMatches value).filter fun p => price p ≤ 20

def matchingProducts (value : ⟦basket⟧) : List Product :=
  (affordable value).filter fun p =>
    (productName p).toLower.contains (value .filters .search).toLower

def visibleProducts (value : ⟦basket⟧) : List Product :=
  (matchingProducts value).mergeSort fun left right =>
    match value .filters .sort with
    | .name => productName left ≤ productName right
    | .priceLow => price left ≤ price right
    | .priceHigh => price right ≤ price left

def total (value : ⟦basket⟧) : Nat := ((value .items).map subtotal).sum

def totalText (value : ⟦basket⟧) : String := s!"Basket total: EUR {total value}"

def matchText (value : ⟦basket⟧) : String := s!"{(visibleProducts value).length} products match"

def catalogueColumns : List (Column product) :=
  [{ label := "Product", format := productName },
   { label := "Category", format := categories.label ∘ category },
   { label := "Price (EUR)", format := toString ∘ price }]

def columns : List (Column item) :=
  [{ label := "Product", format := fun value => productName (value .product) },
   { label := "Qty", format := fun value => toString (value .quantity) },
   { label := "Subtotal (EUR)", format := toString ∘ subtotal }]

def filtersEditor {state : DataType} : Component.Builder state filters :=
  Component.Builder.group "Find products" fun
    | .search => Component.Builder.field "Search" .textInput
    | .category => Component.Builder.field "Category" .select
    | .budget => Component.Builder.field "Price limit" .select
    | .sort => Component.Builder.field "Sort" .select

inductive ItemSection where
  | product
  | quantity
  | decrement
  | increment
  | reset
  | price
  deriving DecidableEq

instance : FinEnum ItemSection :=
  FinEnum.ofList [.product, .quantity, .decrement, .increment, .reset, .price] (by grind [ItemSection])

def itemSections : Enum where
  type := ItemSection
  label
    | .product => "Product"
    | .quantity => "Quantity"
    | .decrement => "−1"
    | .increment => "+1"
    | .reset => "Reset"
    | .price => "Price"

def itemComponent : Component item :=
  .stack (some "Item") (items := itemSections) (fun
    | .product => .field (.field .product .self) "Product" .select
    | .quantity => .field (.field .quantity .self) "Quantity" .naturalInput
    | .decrement => .button "−1" (.decrement (.field .quantity .self))
    | .increment => .button "+1" (.increment (.field .quantity .self))
    | .reset => .button "Reset quantity" (.set (.field .quantity .self) (fun _ => 0))
    | .price => .computed (result := .natural) "Unit price (EUR)" unitPrice)

def boundItems : Component basket :=
  .list itemsPath "Basket" itemComponent (line .notebook 1)

def selectedItem (value : ⟦basket⟧) : ⟦item⟧ := line (value .selected) 1

def addSelected : Component basket := .button "Add selected product" (.append itemsPath selectedItem)

def onPage (page : Page) (value : ⟦basket⟧) : Bool := page == value .page

inductive Section where
  | total
  | page
  | filters
  | matches
  | catalogue
  | selected
  | add
  | items
  | subtotals
  deriving DecidableEq
instance : FinEnum Section :=
  FinEnum.ofList [.total, .page, .filters, .matches, .catalogue, .selected, .add, .items, .subtotals]
    (by intro s; cases s <;> simp)
def sections : Enum where
  type := Section
  label
    | .total => "Total"
    | .page => "Page"
    | .filters => "Filters"
    | .matches => "Matches"
    | .catalogue => "Catalogue"
    | .selected => "Selected product"
    | .add => "Add"
    | .items => "Items"
    | .subtotals => "Subtotals"

def basketView : Component basket := .stack none (items := sections) fun
  | .total => .text totalText
  | .page => .field (.field .page .self) "Page" .select
  | .filters => .visibleWhen (onPage .catalogue) (filtersEditor filtersPath)
  | .matches => .visibleWhen (onPage .catalogue) (.text matchText)
  | .catalogue => .visibleWhen (onPage .catalogue) (.table (row := product) visibleProducts catalogueColumns)
  | .selected => .visibleWhen (onPage .catalogue)
      (.field (.field .selected .self) "Product to add" .select)
  | .add => .visibleWhen (onPage .catalogue) addSelected
  | .items => .visibleWhen (onPage .basket) boundItems
  | .subtotals => .visibleWhen (onPage .basket) (.table (row := item) itemsPath.get columns)

end Forms.ExampleForms.Basket
