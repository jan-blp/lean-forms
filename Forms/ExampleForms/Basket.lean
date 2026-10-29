import Forms.Core.Component.Builder

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

def productName : Expr product .text := .enumLabel (.project .self)
def productPrice : Expr product .natural :=
  .enumCases (.project .self) fun p => .value (price p)
def productCategory : Expr product (.enum categories) :=
  .enumCases (.project .self) fun p => .value (category p)

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

def unitPrice : Expr item .natural :=
  .enumCases (.project (.field .product .self)) fun p => .value (price p)
def subtotal : Expr item .natural :=
  .natMul (.project (.field .quantity .self)) unitPrice

inductive Page where
  | catalogue
  | basket
  deriving DecidableEq

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

def categoryMatches : Expr basket (.list product) :=
  .enumCases (.project (.field .filters (.field .category .self))) fun
    | .all => .value (FinEnum.toList Product)
    | .only c => .filter (.value (FinEnum.toList Product)) (.enumEq productCategory (.value c))

def affordable : Expr basket (.list product) :=
  .enumCases (.project (.field .filters (.field .budget .self))) fun
    | .any => categoryMatches
    | .ten => .filter categoryMatches (.natLe productPrice (.value 10))
    | .twenty => .filter categoryMatches (.natLe productPrice (.value 20))

def matchingProducts : Expr basket (.list product) :=
  .search affordable productName (.project (.field .filters (.field .search .self)))

def visibleProducts : Expr basket (.list product) :=
  .enumCases (.project (.field .filters (.field .sort .self))) fun
    | .name => .sortBy matchingProducts productName false
    | .priceLow => .sortNatBy matchingProducts productPrice false
    | .priceHigh => .sortNatBy matchingProducts productPrice true

def total : Expr basket .natural := .sum (.project itemsPath) subtotal

def totalText : Expr basket .text :=
  .textAppend (.value "Basket total: EUR ") (.natToText total)

def matchText : Expr basket .text :=
  .textAppend (.natToText (.length visibleProducts)) (.value " products match")

def catalogueColumns : List (Column product) :=
  [{ label := "Product", format := productName },
   { label := "Category", format := .enumLabel productCategory },
   { label := "Price (EUR)", format := .natToText productPrice }]

def columns : List (Column item) :=
  [{ label := "Product", format := .enumLabel (.project (.field .product .self)) },
   { label := "Qty", format := .natToText (.project (.field .quantity .self)) },
   { label := "Subtotal (EUR)", format := .natToText subtotal }]

def filtersEditor {state : DataType} : Component.Builder state filters :=
  Component.Builder.group "Find products" fun
    | .search => Component.Builder.field "Search" .textInput
    | .category => Component.Builder.field "Category" .select
    | .budget => Component.Builder.field "Price limit" .select
    | .sort => Component.Builder.field "Sort" .select

inductive ItemSection where
  | product
  | quantity
  | price
  deriving DecidableEq

instance : FinEnum ItemSection :=
  FinEnum.ofList [.product, .quantity, .price] (by grind [ItemSection])

def itemSections : Enum where
  type := ItemSection
  label
    | .product => "Product"
    | .quantity => "Quantity"
    | .price => "Price"

def itemComponent : Component item :=
  .stack (some "Item") (items := itemSections) (fun
    | .product => .field (.field .product .self) "Product" .select
    | .quantity => .field (.field .quantity .self) "Quantity" .naturalInput
    | .price => .computed "Unit price (EUR)" unitPrice)

def boundItems : Component basket :=
  .list itemsPath "Basket" itemComponent (line .notebook 1)

def selectedItem : Expr basket item :=
  .enumCases (.project (.field .selected .self)) fun p => .value (line p 1)

def addSelected : Component basket := .appendItemButton "Add selected product" itemsPath selectedItem

def onPage (page : Page) : Expr basket .boolean :=
  .enumEq (.project (.field .page .self)) (.value page)

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
  | .catalogue => .visibleWhen (onPage .catalogue) (.table visibleProducts catalogueColumns)
  | .selected => .visibleWhen (onPage .catalogue)
      (.field (.field .selected .self) "Product to add" .select)
  | .add => .visibleWhen (onPage .catalogue) addSelected
  | .items => .visibleWhen (onPage .basket) boundItems
  | .subtotals => .visibleWhen (onPage .basket) (.table (.project itemsPath) columns)

end Forms.ExampleForms.Basket
