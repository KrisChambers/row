# ROW

Row is a language whose main purpose right now is to explore some idea in the space of typed functional language.
One major interest is in looking at **Row Polymorphism** which is currently used to type Records and Effects.

The language is currently just a small core with minimal sugar or data types. There is no working data type construct or variants most
focus has been on getting a basic tree walking interpreter and then playing around with Hindley Milner + Records and Effects through rows.

I have been primarily using `Types and Programming Languages` By Benjamin Pearce for the core theory and some papers
on effects and extendible records to work out the type system component of this.


## Example

```
effect State a {
  get : () -> a
  set : a -> ()
}

let inc = \a ->
  let x = State.get()
  in perform State.put (x + 1)

let main = \a ->
  let initial = 0 in
  let value = perform State.get()
  in
    (handle inc() with {
      State.get k -> k a a,
      State.set v k -> k () v
    }) initial



