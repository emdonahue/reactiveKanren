# Guide

This guide offers an intuitive overview of reactiveKanren's basic usage. For a complete function reference, consult the [Documentation](DOCUMENTATION.md).

## Installation

reactiveKanren is implemented as a single Javascript module, and can be imported with the following statement:

```javascript
import {RK} from 'path/to/mk.js'
```

Replace ```path/to/mk.js``` with the path to the mk.js module file.

Note that due to the nature of Javascript module loading, you will need to run a local webserver to view your application. One way to achieve this would be to run Python's simple http server and then navigate to the url corresponding to the output of the shell command:

```shell
python3 -m http.server
```

## Templates
Once reactiveKanren is loaded, a simple application can be added to the HTML document as follows:

```javascript
let app = new RK('lorem ipsum');
document.body.append(app.root());
```

This will append the text 'lorem ipsum' to the body of the document. The string argument, 'lorem ipsum', represents the "view template" for this application. The template describes the HTML structure of the entire reactiveKanren application instance. The template may be as simple as a single string, as in this instance, or it may describe an entire single-page application containing dynamic model data.

The following examples illustrate the template syntax for more complicated views. All of these are valid template arguments for the RK constructor:

### Text nodes
```javascript
'lorem ipsum'
```

```html
lorem ipsum
```

### HTML nodes

```javascript
['p', 'lorem ipsum']
```

```html
<p>lorem ipsum</p>
```

### HTML nodes with properties

```javascript
[{tagName: 'p', id: 'content'}, 'lorem ipsum']
```

```html
<p id="content">lorem ipsum</p>
```

### HTML nodes with space-delimited properties

Properties accept an array of strings or an object containing string-boolean pairs. In the former case, the strings are joined together with spaces separating them. In the latter case, keys with ```true``` values will be joined together with spaces. Object keys with falsy values will be ignored:

```javascript
[{tagName: 'p', className: ['class1', 'class2']}, 'lorem ipsum']
```

```javascript
[{tagName: 'p', className: {class1: true, class2: true, class3: false, class4: null}}, 'lorem ipsum']
```

```html
<p class="class1 class2">lorem ipsum</p>
```

### HTML nodes with CSS style properties
Properties also accept objects containing string-string, string-array, and string-object pairs. These are primarily useful for the style property. String-string pairs set the style named by the key to the value. String-array pairs set the style named by the key to the whitespace-delimited concatenation of array elements, which must be strings. String-object pairs set the style named by the key to the whitespace-delimited concatenation of the key names for which the corresponding values are ```true```:

```javascript
[{tagName: 'p', style: {border: '1px solid black'}}, 'lorem ipsum']
```

```javascript
[{tagName: 'p', style: {border: ['1px', 'solid', 'black']}}, 'lorem ipsum']
```

```javascript
[{tagName: 'p', style: {border: {'1px': true, solid: true, black: true}}, 'lorem ipsum']
```

```html
<p style="border: 1px solid black;">lorem ipsum</p>
```

## miniKanren

Dynamic templates can be written using miniKanren, a small logic programming language embedded in Javascript. This section serves as a basic primer for the implementation of miniKanren that serves as a basis for reactiveKanren, but some familiarity with miniKanren and with Scheme or Lisp will be helpful.

### Cons lists
reactiveKanren exports ```list``` and ```cons``` for creating Scheme-style linked lists, which are useful for implementing common miniKanren idioms. Both accept an arbitrary number of arguments and return a list, in the case of ```list``` or a series of linked list segments terminated by the final argument, in the case of ```cons```:

```javascript
import {cons, list} from 'path/to/mk.js';

list(1, 2, 3); // -> (1 2 3)
cons(1, 2, 3); // -> (1 2 . 3)
```

### Unification (eq)
Every expression in the miniKanren language, up to and including an entire program, is referred to as a "goal." When run, a goal returns a stream of answers for subsequent processing by other goals. Each answer represents the set values bound to a set of top level variables called "query variables."

The simplest goal is called unification, which binds variables to values. Assume we have a miniKanren variable ```x```, also known as a "logic" variable to distinguish it from Javascript variables. If we then unify ```x``` with the number 1 using the ```eq``` unification method of logic variables and run the goal:

```javascript
x.eq(1).run(); // -> ((1))
```

we receive a list of answers. Each answer is itself a list of values, and each value corresponds to one of the logic variables we have bound in our goal. In this case, we receive a list containing a single answer, and that answer contains the single value, 1, which we assigned to ```x```.

```eq```, like the other logic variable methods that will be discussed in this section, is a shorthand for passing the logic variable in as the first argument to the more general ```eq``` function, which can also be imported and used directly:

```javascript
import {eq} from 'path/to/mk.js';

eq(x, 1).run(); // -> ((1))
```

Much of the expressivity of logic programming comes from the fact that unification combines conditional logic and data manipulation in a compact form. When complex structures such as arrays or Javascript objects are unified, miniKanren recursively unifies their common properties:

```javascript
eq({a: 1, b: 2}, {a: x}).run(); // -> ((1))
```

Here, unifying the Javascript object ```{a: 1, b: 2}``` with the smaller object ```{a: x}``` recursively unifies the ```a``` property of each object, binding ```x``` to 1 while ignoring the ```b``` property not shared by both objects. This form of unification can be used to easily destructure complex terms based on matching patterns. Note too that unification is symmetric:

```javascript
eq(x, 1); // -> ((1))
eq(1, x); // -> ((1))
```

### Fresh
In order to create a new logic variable, we use ```fresh```:

```javascript
fresh(x => x.eq(1)).run(); // -> ((1))
```

```fresh``` accepts a function of arbitrary arity and calls that function with a new logic variable for each argument in the function.

### Conj
The ```conj``` method runs multiple goals in the context of the same answer.

```javascript
fresh((x, y, z) => x.eq(1).conj(y.eq(2), z.eq(3))).run(); // -> ((1 2 3))
```

Here we receive a single answer, but each of the three unifications has bound its respective variable within that answer. ```conj``` accepts an arbitrary number of subgoals.

Anywhere a goal can appear in reactiveKanren, an array of goals can be substituted instead, which will be interpreted as a conjunction of all contained goals:

```javascript
fresh((x, y, z) => [x.eq(1), y.eq(2), z.eq(3)]).run(); // -> ((1 2 3))
```

Note that a variable can only have a single value within a single answer:

```javascript
fresh(x => x.eq(1).conj(x.eq(2))).run(); // -> ()
```

This goal returned an empty stream containing no answers because ```x``` cannot have both 1 and 2 as values within a single answer. 

### Conde
```conde``` creates multiple answers and runs each of its subgoals in the context of a new answer:

```javascript
fresh(x => x.eq(1).conde(x.eq(2), x.eq(3))).run(); // -> ((1) (2) (3))
```

Like ```conj```, ```conde``` accepts an arbitrary number of goals and runs them all. In this case, it runs three unifications, which bind ```x``` to 1, 2, or 3, each in a separate answer so as to avoid conflicts.

## Dynamic Templates
In order to generate a dynamic view that displays and allows users to interact with application data, we can inject miniKanren into our view template in the form of a dynamic template.

### Variable Templates
First, we must load some dynamic data into the application. This is done through the optional second argument to the ```RK``` constructor:

```javascript
let app = new RK(model => model, 'lorem ipsum);
document.body.append(app.root());
```

In this example, the string 'lorem ipsum' represents our applicaion's model data. The first argument to the constructor has been replaced with a single-argument function that accepts a logic variable bound to our application's model data, in this case, `lorem ipsum'. The simplest dynamic template is the variable template, which consists simply of a variable bound to a valid reactiveKanren template. Because ```model``` is bound to 'lorem ipsum', and strings are valid templates, ```model``` will be replaced by 'lorem ipsum' and template processing will proceed as normal, injecting the text node `lorem ipsum' into the document body.

### Goal Templates

### Function Templates