# Object proposal

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

#### Syntax: The following are the new syntax forms added to the language with respect to object oriented programming
       
        # Defining a class.
        class Point2D:
            fields x, y
            ...
        end
        
        # Defining a class that extends base class
        class Point3D extends Point2:
            fields z
            ...
        end
        
        # Defining a class with both fields and methods
        class Point2D:
            fields x, y
         
            def get_x(self):  # Self is a keyword, used to refer current instance
               self.x
          
            def get_y(self):
               self.y
        end
        
       
        # Defining a Constructor for classes, to instantiate classes
        
        class Point2D:
            fields x, y
            
            Point2D(x, y):
               self.x = x
               self.y = y
            
            def get_x(self):
               self.x
               
            def get_y(self):
               self.y
               
               
        
        # Creating objects of classes using new keyword which is a reserved keyword.
            point_1 = new Point2D(1, 2)
            point_2 = new Point2D(2, 1)
           
          
       # Accessing fields using DOT operator, DOT operator has a special purpose and is used only to access
       # object fields or methods.
            x1 = point_1.x
            y1 = point_1.y
         
       # Accessing methods using DOT operator
            x = point_1.get_x()
            y = point_1.get_y()
            
            
       # Overriding methods in the derived class, overrided methods have to be of the same signature 
       # as of the base class.
       # Derived class TogglePoint2D has the fields x and y inherited from Point2D class and new definitions
       # for get_x and get_y.
       
          class TogglePoint2D extends Point2D:
                
                def get_x(self):
                    self.y
                
                def get_y(self):
                     self.x
          
          
       # Multiple level inheritance is supported by our language. 
       # Class cat will have all the fields and methods of its base class and,
       # its base class's base class and so on until we find a class that does not extend any class.
       # Our language is also going to support dynamic dispatch to deal with polymorphic functions.
       
           class Animal:
                 fields name, legs, weight, habitat
                 
                 def get_name(self):
                     self.name
                  
                 def get_legs(self):
                     self.legs
                     
                 def get_weight(self):
                     self.weight
                     
                 def get_habitat(self):
                     self.habitat
                     
           class DomesticAnimal extends Animal:
                 fields owner
               
                 def has_owner(self):
                  self.owner
                  
                 def owned_by(self, owner):
                     self.owner = owner
                     
           class Cat extends DomesticAnimal:
                 fields color
                  
                 def has_color(self):
                     self.color
                     
                   
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
            fields val, next
            
            Node(self, val):
               self.val = val
               self.next = nil
               
        class List:
            # head, tail, curr are fields of Node type.
            # There is no static type checking to infer the types of these fields.
            fields head, tail, curr, size  
            
            List(self):
               self.head = nil, self.tail=nil, self.curr=nil, self.size=0
               
            def add(self, val):
                  curr.next = new Node(val), curr = curr.next, size = size + 1
                  
            def size(self):
                self.size
       
            def isEmpty(self):
               self.size == 0
               
            def first(self):
               self.head
            
            def rest(self):
               self.next
               
        
        let list_of_first_100_even_numbers = range(1, 100, 2, nil) in
            sum(list_of_first_100_even_numbers)
            
       
    2. Parser - TODO: Add corresponding AST.
    3. Well formedness : TODO: Add wellformedness checks
    4. Static Typing: 
    5. Tagging: 
    6. Anfing
    7. Compilation of Objects
       - Replacing tuples in Fer-de-lance and instead reusing tuples tagging scheme for objects. 
       
    
## Timeline: 
We are diving our project deliverables into two parts. 
### Phase 1: 
In phase 1, we are going to implement records first and then extend it to classes. The end of first phase will include testing the compilation part with different AST representations.
### Phase 2: 
In the phase 2, we are going to focus on getting from the syntax to the AST representation. And test end to end user programs.

In the final write up we are going to mention changes in all phases that includes wellformedness, tagging and static typing. These additional compiler phases focusing on robustness will be added in the actual implementation depending on where we are in the timeline. However our report is going to be detailed wrt to what needs to change. 
