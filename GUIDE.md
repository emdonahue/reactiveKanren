# Guide

This guide offers an intuitive overview of reactiveKanren's basic usage. For a complete function reference, consult the [Documentation](DOCUMENTATION.md).

## Installation

reactiveKanren is implemented as a single Javascript module, and can be imported with the following statement:

```javascript
import RK from 'path/to/mk.js'
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
reactiveKanren exports ```list``` and ```cons``` for creating Scheme-style linked lists, which are useful for implementing common miniKanren idioms. Both accept an arbitrary number of arguments and return a list, in the case of ```list``` or a series of linked list segments terminated by the final argument, in the case of ```cons```. All exported functions can also be accessed as static properties of the main RK object:

```javascript
import {default as RK, cons, list} from 'path/to/mk.js';

list(1, 2, 3); // -> (1 2 3)
RK.list(1, 2, 3); // -> (1 2 3)

cons(1, 2, 3); // -> (1 2 . 3)
RK.cons(1, 2, 3); // -> (1 2 . 3)
```

### miniKanren goals
Every expression in the miniKanren language, up to and including an entire program, is referred to as a "goal." When run, a goal returns a stream of answers. The simplest goal is called unification, which assigns variables to values. Assume we have a miniKanren variable ```x```, also known as a "logic" variable. If we then unify ```x``` with the number 1 using the ```eq``` unification method of logic variables and run the goal:

```javascript
x.eq
```

we receive a list of answers