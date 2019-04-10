# Object Oriented Programming.

### Goal : Using a simplified version of Fer-de-lance and extending the language by adding support for Object Oriented Programming.

### Features: 
   
   The following are some of the features that are going to be added to the language.
 
    1. Classes definitions and constructors
    2. self
    3. Methods
    4. Fields
    5. Dynamic dispatch
    6. Inheritance - single and multilevel
    7. Overriding
    8. instanceof  
    
## Compiler Pipeline: 

Introducing objects and classes in our language is going to affect all phases of compilation. 
The following are the phases affected  by this new feature and changes in them.

#### Grammer: 
      <dec> : 
       | <classdec>
      <classdec> : 
       | class IDENTIFIER <classfields>
       | class IDENTIFIER extends IDENTIFIER <classfields>
      <classfields> :
       | <classfield>
       | <classfield> <classfields>
      <classfield> : 
       | <field>
       | <method>
      <method> :
       | method IDENTIFIER(<ids>) : <exp>
       | method IDENTIFIER(<ids>) -> <typ> : <exp>
      <field> :
       | field IDENTIFIER
       | field <bind>
      <exprs> : 
       | ...
       | new IDENTIFIER()
       | <obj-get>
       | <obj-set>
      <obj-get> :
       | IDENTIFIER.IDENTIFIER
       | <obj-get>.IDENTIFIER
      <obj-set> :
       | <obj-get> := <expr>
      
#### Syntax: The following are the new syntax forms added to the language with respect to object oriented programming
       
        # Defining a class.
        class Point2D:
            field x
            field y
            ...
        end
        
        # Defining a class that extends base class
        class Point3D extends Point2:
            field z
            ...
        end
        
        # Defining a class with both fields and methods
        class Point2D:
            field x
            field y
         
            method get_x(self):  
               self.x
          
            method get_y(self):
               self.y
        end
        
       # Defining a class with both fields and methods with type annotation s
        class Point2D:
            field x : int 
            field y : int
         
            method get_x(self) -> int:  
               self.x
          
            method get_y(self) -> int:
               self.y
        end
                       
        
        # Creating objects of classes using new keyword which is a reserved keyword.
            point_1 = new Point2D()
            
        # setting the fields
            point_1.x := 1
            point_1.y := 2
           
          
       # Accessing fields using DOT operator, DOT operator has a special purpose and is used only to access
       # object fields or methods.
            x1 := point_1.x
            y1 := point_1.y
         
       # Accessing methods using DOT operator
            x := point_1.get_x()
            y := point_1.get_y()
            
            
       # Overriding methods in the derived class, overrided methods have to be of the same signature 
       # as of the base class.
       # Derived class TogglePoint2D has the fields x and y inherited from Point2D class and new definitions
       # for get_x and get_y.
       
          class TogglePoint2D extends Point2D:
                
                method get_x(self):
                    self.y := x;
                    self.x
                
                method get_y(self):
                     self.x := y;
                     self.y
          
         end
       # Multiple level inheritance is supported by our language. 
       # Class cat will have all the fields and methods of its base class and,
       # its base class's base class and so on until we find a class that does not extend any class.
       # Our language is also going to support dynamic dispatch to deal with polymorphic functions.
       
           class Animal: # All base classes extends Object class.
                 fields name, legs, weight, habitat
                 
                 method get_name(self):
                     self.name
                  
                 method get_legs(self):
                     self.legs
                     
                 method get_weight(self):
                     self.weight
                     
                 method get_habitat(self):
                     self.habitat
           end          
           
           class DomesticAnimal extends Animal:
                 field owner
               
                 method has_owner(self):
                  self.owner
                  
                 method owned_by(self, owner):
                     self.owner := owner
           end        
           class Cat extends DomesticAnimal:
                 field color
                  
                 method has_color(self):
                     self.color
           end        
                   
       # Definition of Program has changed from  being a collection of function groups
       # to a collection of function group and classes.
       # For example the following is an example program in our language where we can create
       # a linked list of numbers and using range and then also sum all the number using sum
       
        def range(start, end, step, list):
            if start == end:
               list
            else:
               range(start + step, end, step, (if list == nil : new Node(start) else: (list.next = new Node(start), list))
               
        def sum(list):
            if list == nil : 0 else: list.first().val + sum(list.rest())
                 
            
        class Node:
            field val
            field next
        end    
        
        class List:
            # head, tail, curr are fields of Node type.
            # There is no static type checking to infer the types of these fields.
            field head
            field tail
            field curr
            field size 
               
            method add(self, val):
                  curr.next := new Node(val); curr := curr.next; size := size + 1
                  
            method size(self):
                self.size
       
            method isEmpty(self):
               self.size == 0
               
            method first(self):
               self.head
            
            method rest(self):
               self.next
               
        end
        
        let list_of_first_100_even_numbers = range(1, 100, 2, nil) in
            sum(list_of_first_100_even_numbers)
            
#### Parser: Extension of the AST.
            
               type 'a typ =
                 | TyBlank of 'a
                 | TyCon of string * 'a
                 | TyVar of string * 'a
                 | TyArr of 'a typ list * 'a typ * 'a
                 | TyApp of 'a typ * 'a typ list * 'a
                 | TyTup of 'a typ list * 'a

               type 'a scheme =
                 | SForall of string list * 'a typ * 'a

               and 'a bind =
                 | BBlank of 'a typ * 'a
                 | BName of string * 'a typ * 'a
                 | BTuple of 'a bind list * 'a

               and 'a binding = ('a bind * 'a expr * 'a)

               and 'a expr =
                    | ESeq of 'a expr * 'a expr * 'a
                    | ETuple of 'a expr list * 'a
                    | EGetItem of 'a expr * int * int * 'a
                    | ESetItem of 'a expr * int * int * 'a expr * 'a
                    | ELet of 'a binding list * 'a expr * 'a
                    | ELetRec of 'a binding list * 'a expr * 'a
                    | EPrim1 of prim1 * 'a expr * 'a
                    | EPrim2 of prim2 * 'a expr * 'a expr * 'a
                    | EIf of 'a expr * 'a expr * 'a expr * 'a
                    | ENumber of int * 'a
                    | EBool of bool * 'a
                    | ENil of 'a typ * 'a
                    | EId of string * 'a
                    | EApp of 'a expr * 'a expr list * 'a
                    | ELambda of 'a bind list * 'a expr * 'a
                    | EAnnot of 'a expr * 'a typ * 'a
                    | EGetObj of 'a expr * string * 'a
                    | ESetObj of 'a expr * string * 'a expr * 'a
                    | ENew of String * 'a
                   
               and  type 'a decl =
                 | DFun of string * 'a bind list * 'a scheme * 'a expr * 'a

               and type 'a tydecl =
                 | TyDecl of string * 'a typ list * 'a
                                            
               and type 'a classDecl =
                  | Class of string * string *  'a bind list * 'a decl list * 'a
               
               and type 'a program =
                  | Program of 'a classdecl list * 'a tydecl list * 'a decl list list * 'a expr * 'a

              
    
#### Well formedness:
             1. extends <IDENTIFIER> where IDENTIFIER is a class.
             2. Method names should be unique
             3. Method argument ids should be unique
             4. first argument to a method must be 'self'
             5. Field names should be unique
             6. self is keyword
             7. new is a keyword
             8. <IDENTIFIER> . <IDENTIFIER> , before . should be a class and after . should be a field in class
             9. <IDENTIFIER> . <IDENTIFIER> (x, y, z) before . should be a class and after . should be a method in class with same arity
            10: <IDENTIFIER> . <IDENTIFIER> := <something> mutation is only possible for class fields.
            
#### Type system : Not going to be implemented for the purpose of the project.

#### Tagging : 

#### Anfing :

                  type 'a immexpr = (* immediate expressions *)
                    | ImmNum of int * 'a
                    | ImmBool of bool * 'a
                    | ImmId of string * 'a
                    | ImmNil of 'a
                  and 'a cexpr = (* compound expressions *)
                    | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
                    | CPrim1 of prim1 * 'a immexpr * 'a
                    | CPrim2 of prim2 * 'a immexpr * 'a immexpr * 'a
                    | CApp of 'a immexpr * 'a immexpr list * 'a
                    | CImmExpr of 'a immexpr (* for when you just need an immediate value *)
                    | CTuple of 'a immexpr list * 'a
                    | CGetItem of 'a immexpr * int * 'a
                    | CSetItem of 'a immexpr * int * 'a immexpr * 'a
                    | CLambda of string list * 'a aexpr * 'a  
                    | CInitObj of string * 'a
                    | CGetObj of 'a immexpr * string * 'a  // this can return both a field or a closure.
                    | CSetObj of 'a immexpr * string * 'a immexpr * 'a // we will only have fields for mutation
                 and 'a aexpr = (* anf expressions *)
                    | ASeq of 'a cexpr * 'a aexpr * 'a
                    | ALet of string * 'a cexpr * 'a aexpr * 'a
                    | ALetRec of (string * 'a cexpr) list * 'a aexpr * 'a
                    | ACExpr of 'a cexpr
                  and 'a adecl =
                    | ADFun of string * string list * 'a aexpr * 'a
                  and 'a aclassdecl =
                    | AClass of string * string *  'a bind list * 'a adecl list * 'a
                  and 'a aprogram =
                    | AProgram of 'a aclassdecl list * 'a adecl list * 'a aexpr * 'a
                  ;;
#### Compilation of Objects

#### 1. class
We store class information in class descriptors, which stores class methods. If a class is inheritated from a base class, the class descriptor should have a pointer to the class descriptor of its base class. For a class

```
class Base
  fields x, y
  def bar(self):
      ...
  def baz(self):
      ...
end
```
A class descriptor should be created on the heap:
```
| base | N | bar | baz |
```
where base is a pointer to its base class, N is the number of class methods. base should be null if the class has no base class.

To handle single inheritance, the class descriptor of the inheritated class should have a pointer to the base class. For the class Der,

```
class Der extends Base
  fields z
  def bar(self):
      ...
  def der(self):
      ...
end
```

Its class descriptor should be like
```
| Base | N | bar | baz | der |
```
where bar should point to the method defined in Der instead of Base.

When a method is being called, like
```
b.bar()
```
First the lookup the class descriptor, which is stored in instance b. With the class descriptor, lookup the method at an offset from the start of the class descriptor. The offset is calculated at compile time. The method is a lambda expression, which can be applied.

#### 2. Instance variables
Class variables are compiled similar to tuples. For a class
```
class Base
  fields x, y
end
```
An instance is stored on the heap like,
```
| descriptor | N | x | y |
```
To handle single inheritance, the fields of the base class is are put in the begining of the extended class, followed by the fiels of the base class. For example,
```
class Der extends Base
  fields z
end
```
is stored on the heap like,
```
| descriptor | N  | x | y | z |
```
#### 3. Support for self
Each class method should come with an argument self so the method can refer to class variables and other methods. self is a pointer to the class instance. To implement self, we'll allocate the heap space with dummy values first when instantiating an object, then fill in the real value including self. When an instance method is being called, self would be passed as the first argument.

#### 4. Support for instanceof
We can use the address of the class descriptor to test class membership,
## Timeline: 
We are diving our project deliverables into two parts. 
### Phase 1: 
In phase 1, we are going to implement records first and then extend it to classes. The end of first phase will include testing the compilation part with different AST representations.
### Phase 2: 
In the phase 2, we are going to focus on getting from the syntax to the AST representation. And test end to end user programs.

In the final write up we are going to mention changes in all phases that includes wellformedness, tagging and static typing. These additional compiler phases focusing on robustness will be added in the actual implementation depending on where we are in the timeline. However our report is going to be detailed wrt to what needs to change. 
