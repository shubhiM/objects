# Object proposal

### Goal : Extending Fer-de-lance language by adding support for Object Oriented Programming.
### Features: 
   
   The following are some of the features that are going to be added to the language.
 
    1. this
    2. Methods
    3. Fields
    4. Dynamic dispatch
    5. Inheritance - single level inheritance only.
    6. Overriding
    7. Overloading
    8. instanceof
    9. Classes and constructors
    
## Compiler Pipeline: 

Introducing objects and classes in our language is going to affect all phases of compilation. 
The following are the phases affected  by this new feature and changes in them.


    1. Syntax - TODO: Add new syntax forms
    2. Parser - TODO: Add corresponding AST.
    3. Well formedness : TODO: Add wellformedness checks
    4. Static Typing:
    5. Tagging: 
    6. Anfing
    7. Compilation of Objects
    
## Timeline: 
We are diving our project deliverables into two parts. 
### Phase 1: 
In phase 1, we are going to implement records first and then extend it to classes. The end of first phase will include testing the compilation part with different AST representations.
### Phase 2: 
In the phase 2, we are going to focus on getting from the syntax to the AST representation. And test end to end user programs.

In the final write up we are going to mention changes in all phases that includes wellformedness, tagging and static typing. These additional compiler phases focusing on robustness will be added in the actual implementation depending on where we are in the timeline. However our report is going to be detailed wrt to what needs to change. 
