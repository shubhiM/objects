1. class 
We store class information in class descriptors, which stores class methods. If a class is inheritated from a base class, the class descriptor should have a pointer to the class descriptor of its base class.
For a class
```
class Base
  field x
  field y
  method bar
  method baz
end
```
A class descriptor should be created on the heap:
```
| base | N | bar | baz |
```
where `base` is a pointer to its base class, `N` is the number of class methods. `base` should be null if the class has no base class.

To handle single inheritance, the class descriptor of the inheritated class should have a pointer to the base class. 
For the class `Der`,
```ocaml
class Der extends Base
  field z
  method bar
  method der
end
```
Its class descriptor should be like
```
| Base | N | bar | baz | der |
```
where `bar` should point to the method defined in `Der` instead of `Base`.

When a method is being called, like
```ocaml
b.bar()
```
First the lookup the class descriptor, which is stored in instance `b`. With the class descriptor, lookup the method at an offset from the start of the class descriptor. The offset is calculated at compile time.
The method is a lambda expression, which can be applied.

2. instance variables
Class variables are compiled similar to tuples.
For a class
```
class Base
  field x
  field y
end
```
An instance is stored on the heap like,
```
| descriptor | N | x | y |
```
To handle single inheritance, the fields of the base class is are put in the begining of the extended class, followed by the fiels of the base class.
For example, 
```ocaml
class Der extends Base
  field z
end
```
is stored on the heap like,
```
| descriptor | N  | x | y | z |
```
3. support for `self`
Each class method should come with an argument `self` so the method can refer to class variables and other methods. `self` is a pointer to the class instance.
To implement `self`, we'll allocate the heap space with dummy values first when instantiating an object, then fill in the real value including `self`.
When an instance method is being called, `self` would be passed as the first argument.

4. support for `instanceof`
We can use the address of the class descriptor to test class membership,
