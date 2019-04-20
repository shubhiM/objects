# Object Oriented Programming.

In this project, we are going to add object oriented features to an existing compiler which provides support for expressions, statements, functions, mutually recursive and recursive functions, lambdas, let expressions and sequences. we are going to analyze the changes to be introduced in each phase of the compiler pipeline to implement all the new features and also how the interactions between these new object oriented features and existing forms are going to get impacted.

### Features: 
   
   The following are some of the features that are going to be added to the language.
 
    1. Classes definitions
    2. Constructors - default constructors with no arguments.
    2. self
    3. Methods
    4. Fields
    5. Dynamic dispatch
    6. Inheritance - single and multilevel
    7. Overriding
    
### Grammer: 
The following are the changes in the grammer. We introduce new grammer for defining classes i.e. class fields and class methods and using classes by means of constructing objects, accessing values from objects and mutating objects. In addtion extends is used to indicate inheritance from a base class.

      <decl> : 
       | ...
       | <classdecl>
      <decls>
       | <decl> <decls>
      <classdecl> : 
       | class IDENTIFIER <baseclass>: <classfields> <classmethods>
      <baseclass> : 
       | None
       | extends IDENTIFIER
      <classfields> :
       | <classfield>
       | <classfield> <classfields>
      <classfield> : 
       | field <bind>
      <classmethods>
       | <classmethod>
       | <classmethod> <classmethods>
      <classmethod> :
       | method IDENTIFIER(<binds>) : <expr> 
       | method IDENTIFIER() : <expr> 
      <expr> : 
       | ...
       | new IDENTIFIER()
       | <dot>
       | <dot-app>
       | <dot-set>
      <exprs>
       | <expr> <exprs>
      <dot> :
       | <expr>.IDENTIFIER
      <dot-app> :
       | <expr>.IDENTIFIER()
       | <expr>.IDENTIFIER(<exprs>)
      <dot-set> :
       | <dot> := <expr>
      <program> 
       | <expr>
       | <decls> <expr>
       
       
       
#### user syntax

        (* class definitions *)
        class Point2D:
            field x
            field y
            
            method get_x(self):
               self.x
            
            method get_y(self):
               self.y
        end
        
        class Point3D extends Point2:
            field z
            
            method get_z(self):
               self.z
            
            method set_x(self, x):
               self.x = x
               
            method set_y(self, y):
               self.y = y
            
            method set_z(self, z):
               self.z = z
        end
        
        def merge(point_1, point_2):
            (point_1.get_x() + point_2.get_x() + point_1.y + point_2.y + point_1.get_z() + point_2.z)
        
        let point_1 = new Point3D(), point_2 = new Point3D() in
            (point_1.set_x(1); point_1.set_y(2); point_1.set_z(3);
             point_2.set_x(3); point_1.set_y(2); point_1.set_z(1);
             merge(point_1, point_2))
        
       (* Now you can define your own data structures and liberary functions *)
       (* More useful programs *)
       
        class Node:
            field val
            field next
        end    
        
        class List:
            field head
            field tail
            field curr
            field size 
               
            method add(self, val):
                  (curr.next := new Node(val); curr := curr.next; self.size := self.size + 1)
                  
            method size(self):
                self.size
       
            method isEmpty(self):
               self.size == 0
               
            method first(self):
               self.head
            
            method rest(self):
               self.next
               
        end
         
       def range_helper(start, end, step, head, head):
         if start == end:
            list
         else:
            (list.next := new Node(start); range(start + step, end, step, list.next, list))
          
       def range(start, end, step, head):
         range_helper(start, end, step, head, head)
            
       def sum(list):
            if list == nil : 0 else: list.first().val + sum(list.rest())
        
       let head = new List(), list_of_first_100 = range(1, 100, 2, head) in
            sum(list_of_first_100)
            

###### Note* : Limitations in current implementation enforces that if there are classes in the user program then they must be defined before function declarations and base class be defined before its child classes.

## Compiler Pipeline: 

Introducing objects and classes in our language is going to affect all phases of compilation from parsing to compilation of user code into machine code.

#### Parser: 


#### AST.
            
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

#### 1. Compilation of classes

#### Compilation of Objects


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
