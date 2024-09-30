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

The following examples illustrate the template syntax for more complicated views:

### HTML Nodes

```javascript
['p', 'lorem ipsum']
```

```html
<p>lorem ipsum</p>
```