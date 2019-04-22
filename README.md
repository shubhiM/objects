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

#### Parsing: 
changes in the lexer, addition of new tokens.
            
         rule token = parse 
                 ...
           | "class" { CLASS }
           | "extends" { EXTENDS }
           | "method" { METHOD }
           | "new" { NEW }
           | "field" { FIELD }
           | "." { DOT }
                 
 
 
changes in the parser, addition of new forms
         
             simple_expr :
                ...
               // object cases
               | NEW ID LPARENNOSPACE RPAREN { ENew($2, full_span()) }

               // e dot field access
               | binop_expr DOT ID %prec COLON { EDot($1, $3, full_span()) }

               // e dot applications
                | binop_expr DOT ID LPARENNOSPACE exprs RPAREN { EDotApp($1, $3, $5, full_span()) }
                | binop_expr DOT ID LPARENNOSPACE RPAREN { EDotApp($1, $3, [], full_span()) }

                // e dot field mutations
                | binop_expr DOT ID COLONEQ expr %prec DOT { EDotSet($1, $3, $5, full_span()) }
                                                
             classfield :
               | FIELD ID { BName($2, TyBlank(full_span()), full_span()) }

             classmethod :
               | METHOD ID LPARENNOSPACE RPAREN COLON expr
                  { let arg_pos = Parsing.rhs_start_pos 3, Parsing.rhs_end_pos 4 in
                     DFun($2, [], SForall([], TyArr([], TyBlank arg_pos, arg_pos), arg_pos), $6, full_span()) }
               | METHOD ID LPARENNOSPACE RPAREN THINARROW typ COLON expr
                     {
                      let typ_pos = tok_span(6, 6) in
                      DFun($2, [], SForall([], TyArr([], $6, typ_pos), typ_pos), $8, full_span()) }
               | METHOD ID LPARENNOSPACE binds RPAREN COLON expr
                      {
                        let arg_types = List.map bind_to_typ $4 in
                        let typ_pos = tok_span(3, 5) in
                        let arr_typ = SForall([], TyArr(arg_types, TyBlank(typ_pos), typ_pos), typ_pos) in
                        DFun($2, $4, arr_typ, $7, full_span())
                      }
               | METHOD ID LPARENNOSPACE binds RPAREN THINARROW typ COLON expr
                       {
                          let arg_types = List.map bind_to_typ $4 in
                           let typ_pos = tok_span(3, 7) in
                           DFun($2, $4, SForall([], TyArr(arg_types, $7, typ_pos), typ_pos), $9, full_span())
                        }

             classfields :
                | { [] }
                | classfield classfields { $1 :: $2 }

             classmethods :
                | { [] }
                | classmethod classmethods { $1 :: $2 }

             classdecl :
                | CLASS ID superclass COLON classfields classmethods END { Class($2, $3, $5, $6, full_span()) }

             superclass :
                | { None }
                | EXTENDS ID { Some $2 }

              classdecls:
                 | { [] }
                 | classdecl classdecls { $1 :: $2 }
                          
              program :
                 | tydecls classdecls decls expr COLON typ EOF { Program($1, $2, $3, EAnnot($4, $6, tok_span(4, 6)), full_span()) }
                 | tydecls classdecls decls expr EOF { Program($1, $2, $3, $4, full_span()) }             
                              
                              
                 


#### AST.
              and 'a bind =
                 ...
                 | BName of string * 'a typ * 'a
              and 'a binding = ('a bind * 'a expr * 'a)
              and 'a typ =
                 ...
                 (* Discussed in detail in the type system section *)
                 | TyClass of 'a bind list * 'a bind list * 'a
              and 'a expr =
                  ...
                 (* Accessing field on a class object *)
                 | EDot of 'a expr * string * 'a 
                 
                 (* Calling method from a class object x.foo() x.foo(1, 2, 3) *)
                 | EDotApp of 'a expr * string * 'a expr list * 'a 
                 
                 (* Mutating fields on a class object *)
                 | EDotSet of 'a expr * string * 'a expr * 'a 
                 
                 (* Constructing a new Object *)
                 | ENew of string * 'a
                                            
              type 'a classDecl =
                 | Class of string * string option *  'a bind list * 'a decl list * 'a
               
              type 'a program =
                 | Program of 'a tydecl list * 'a classdecl list * 'a decl list list * 'a expr * 'a

#### Well formedness:
             1. extends <IDENTIFIER> where IDENTIFIER needs to exist.
             2. Method names should be unique
             3. Method argument ids should be unique
             4. first argument to a method must be 'self'
             5. Field names should be unique
             7. new is a keyword
             8. <IDENTIFIER> . <IDENTIFIER> , both identifiers should be in scope.
             9. <IDENTIFIER> . <IDENTIFIER> (x, y, z)  identifiers should be in scope and function arity should be correct.
            10: <IDENTIFIER> . <IDENTIFIER> := <something> both indentifiers should be in scope.
            
#### ResolveObjTypes : 
A new phase is introduced in the compiler pipeline in which we instantiate a TyClass Type for each class definition and also bind this type wherever object is created. Thus, for every object we create we have an information about its class/Type and also an environment in which we map this object with its associated type. The object - TyClass mapping in environment is used to desugar getters and setters on objects to directory contain offset instead of respective field or method name. Going forward we use these desugared syntax forms to anf and compile the program.

1.  TyClass
 TyClass will get created for each class definition. TyClass(class_name, field_types, method_types, pos) where field_types and         method_types are both 'a bind list and classname is a string
 
        
         | TyClass of string * 'a bind list * 'a bind list * 'a 
       
    
   Example: TyClass for Point2D class introduced above.
                 
                 field_types_2D = [BName(x, TyCon(int, pos), pos);
                                   BName(y, TyCon(int, pos), pos)]
                 
                 nothing_to_int =  TyArr([TyBlank(pos)], TyCon(int, pos), pos)
                 
                 method_types_2D = [BName(get_x, nothing_to_int , pos); 
                                    BName(get_y, nothing_to_int, pos)]
                 
                 class  ----> class Type
                 Point2D  -> TyClass(Point2D, field_types_2D, method_types_2D, pos)
        
   
   Example: TyClass for Point3D class introduced above. In case of inheritance, base class fields and methods come before the sub class fields and methods in TyClass definition. This design choice enables us to support overriding of fields and methods and sharing resources between base class and sub class.
   
                
                 field_types_3D = [BName(x, TyCon(int, pos), pos);
                                BName(y, TyCon(int, pos), pos); 
                                BName(z, TyCon(int, pos), pos)]
                 
                 nothing_to_int = TyArr([TyBlank(pos)], TyCon(int, pos), pos)
                 
                 int_to_class =  TyArr([TyCon(int, pos)], Point2D , pos)
                 
                 method_types_3D = [BName(get_x, nothing_to_int , pos); 
                                 BName(get_y, nothing_to_int, pos); 
                                 BName(get_z, nothing_to_int, pos);
                                 BName(set_x, int_to_class , pos);
                                 BName(set_y, int_to_class , pos);
                                 BName(set_z, int_to_class , pos)]
                 
                 TyClass(Point3D, field_types_3D, method_types_3D, pos)
   

2.  Creating a class environment and passing it along in the program. Class environment is 'a typ envt. 
     
                       Program(tydecls, classes, declgroups, main, pos) ->
                          let new_class_env = List.fold_left
                            (fun env cls ->
                                match cls with
                                |Class(name, base, fields, methods, tag) ->
                                 let class_type = (type_of_this cls env) in
                                 (name, class_type)::env)
                          []
                          classes
                          in
                          let new_declgroups = List.map (fun g -> (helpG g new_class_env)) declgroups in
                          let new_main = helpE main new_class_env in
                          Program(tydecls, classes, new_declgroups, new_main, pos)
                         

3. Updating let bindings to contain this new TyClass type for each class definition and updating object -> TyClass mapping
in the environment.

               let rec new_let_bindings (bindings : ('a bind * 'a expr * 'a) list) (env : 'a typ envt) =
                       (* for every binding ('a bind * 'a expr * 'a)
                          for every bind BName of string * 'a typ * 'a
                          if the expr is ENew then get the TyRecord from the class environment.
                       *)
                       List.fold_left
                       (fun (new_b, env) (bind, expr, pos1) ->
                           match bind with
                           | BName(name, typ, pos2) ->
                             (
                               match expr with
                                 |ENew(class_name, loc) ->
                                   let t = (find env class_name (string_of_sourcespan loc)) in
                                   (new_b @ [(BName(name, t, pos2), helpE expr env, pos1)], (name, t)::env)
                                 | _ -> (new_b @ [(bind, expr, pos1)], env) (* keep as it is *)
                             )
                           | _ -> (new_b @ [(bind, expr, pos1)], env) (* keep as it is *)
                       )
                       ([], env)
                       bindings
                in
                let helpE (e : sourcespan expr) (env : sourcespan typ envt) : sourcespan expr =
                     match e with
                     | ELet (bindings, body, loc) ->
                         let (new_bindings, env) = (new_let_bindings bindings env) in
                         ELet(new_bindings, (helpE body env), loc)
                
               
3. Desugaring ENew to ETuple, EDot to EGetItem, EDotApp to EApp and EDotSet to ESetItem. Reusing Tuples AST for classes. 

   ENew now becomes ETuple. 
                          
                          
                          (4 bytes)    (4 bytes)        (4 bytes)  .................... (4 bytes)
                          -----------------------------------------------------------------------
                          | # size | base class VTable | element_0 | element_1 | ... | element_n |
                          ------------------------------------------------------------------------
                          size is the number of elements in the object.
                          base class VTable is used to access the class descriptor for method calling.
                          
                         | ENew(classname, loc) ->
                               let classtype = find env classname (string_of_sourcespan loc) in
                               let (name, vars) = match classtype with
                                   | TyClass(cname, fields, methods, loc) ->
                                       (cname, List.map (fun _ -> ENumber(0, loc)) fields)
                               in
                               ETuple(EId(name, loc)::vars , loc)
                               
   EDot becomes EGetItem(expr, field_offset, 0, loc) where we are not using size semantically, it is serving like a flag size    = 0 means that we are accessing a field on an object.                         
                               
                           | EDot(expr, id, loc) ->
                               let classname = name_of_expr expr in
                               let classtype = find env classname (string_of_sourcespan loc) in
                               let offset = match classtype with
                                   | TyClass(cname, fields, methods, _) ->
                                       find_index id fields
                               in
                               EGetItem(expr, offset+1, 0, loc)
                           
   EDotApp becomes call to a Lambda expression EGetItem(vtable , method_offset, -1, loc) with method arguments enclosed in the    function call. size is set to -1 to indicate that it is a method access and not a field access.
   
                           | EDotApp(expr, id, args, loc) ->
                               let classname = name_of_expr expr in
                               let classtype = find env classname (string_of_sourcespan loc) in
                               let (name, offset) =
                                   match classtype with
                                   | TyClass(cname, fields, methods, _) ->
                                       (cname, find_index id methods)
                               in
                               let vtable = EId(name, loc) in
                               let args = expr::args in
                               EApp(EGetItem(vtable, offset+1, -1, loc), args, loc)
 
 
 EDotSet becomes ESetItem(expr, offset + 1, 0, newval, loc).                     
                       
                           | EDotSet(expr, id, newval, loc) ->
                               let classname = name_of_expr expr in
                               let classtype = find env classname (string_of_sourcespan loc) in
                               let offset = match classtype with
                                   | TyClass(cname, fields, methods, _) ->
                                       find_index id fields
                               in
                               ESetItem(expr, offset + 1, 0, newval, loc)


#### Anfing : Program is changed to add a new type for class and compound expressions are changed to add new types for Object creation, accessors and gettors. 
       
                  and 'a cexpr = (* compound expressions *)
                     ... 
                    | CTuple of 'a immexpr list * 'a
                    | CGetItem of 'a immexpr * int * 'a
                    | CSetItem of 'a immexpr * int * 'a immexpr * 'a
                  
                  and 'a aclassdecl =
                    | AClass of string * string *  'a bind list * 'a adecl list * 'a
                  
                  and 'a aprogram =
                    | AProgram of 'a aclassdecl list * 'a adecl list * 'a aexpr * 'a
                  ;;

#### Compilation : 
  
##### Compilation of Classes
   1. Program compilation order changes, we first compile classes so we have class descriptors available before compiling methods and the main body.
   
   2. We add class Names to the initial environment. Initial environment is of the form (string * arg) list. Class Names are         converted to LabelContents.
   
          let initial_env =
               List.fold_left
                     (fun env c -> match c with
                             | AClass(name, _, _, _, _) -> (name, LabelContents(name))::env)
                      initial_env classdecls
          in
  
  3. We create a section .data to create  global for each class in the data section.
               
               let data_section =
                 List.fold_left
                   (fun str c -> match c with
                                     | AClass(name, _, _, _, _) -> (sprintf "%s%s dd 0\n" str name))
                 "section .data\n" classdecls
               in
           
  4. We compile Classes to VTables and move the ESI address to the global for that class.
  

            (4 bytes)
            ---------------------------------------------------------------
            | N      | pointer_to_vtable | method_1 | method_2 | method_n |
            ----------------------------------------------------------------
            
   
        4.1. compile methods as lambdas

        4.2. allocate space for vtable

        4.3. set the header and put the address of lambdas on the vtable

        4.4.  save the address of vtable as a global variable
           
           
#####  Compilation of Instance Variables.

   1.  Class variables are compiled similar to tuples. For a class
                  
                  
                  class Base
                    fields x, y
                  end
                
                
                  An instance is stored on the heap like,
                  
                  ---------------------------------------
                  | N  | pointer_to_vtable | x   | y    |
                  
                  ----------------------------------------

  2. To handle multilevel inheritance, the fields of the base class are put before the extended class. For example.
  

                  class Der extends Base
                    fields z
                  end

                  is stored on the heap like,
                 
                  ---------------------------------------------------
                  | N    | pointer_to_vtable  | x   | y    | z     |
                  
                  ---------------------------------------------------

#### 3. Support for self
Each class method should come with an argument self so the method can refer to class variables and other methods. self is a pointer to the class instance. To implement self, we'll allocate the heap space with dummy values first when instantiating an object, then fill in the real value including self. When an instance method is being called, self would be passed as the first argument.


Some Implementation and design notes.


Implementation choices :
  - Syntax choices to represent the object creation, getters and setters.
  - Objects and classes representation
  - Mutation of class fields returns the mutated class object.
  - Single vs Mulitple inheritance
  - TyClass {name, fields , methods} - allows us flexibility to add type inference later.
  - Desugar the object oriented AST to tuple expressions, allows us to reuse the implementation from Tuples.
  - storing class descriptors in section .data as globals, allows us to implement inheritance and overriding.

 Interesting semantics :
   1. mutation returns the object unlike side effects which dont return anything. 
   2. semantics inheritance of field_names, base class field names come before sub class in TyClass.
   
  Design consequences :
   
   1. classes definition comes before global functions
   2. base class comes before sub class
   3. Support for Multiple inheritance is difficult in future.
   4. Support for monkey patching in future is possible
   5. Support for type inference for class objects is possible in future.
