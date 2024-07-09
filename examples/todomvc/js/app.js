import {RK, nil, LVar, SVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify, conj, fail, render as render, view} from '../../../mk.js'

import {logging} from '../../../util.js';

(function (window) {
	'use strict';

    let data = {todos: list({title: 'mytodo'})}
    
    let template =
        [{tagName: 'section', className: 'todoapp'},
         [{tagName: 'header', className: 'header'},
          ['h1', 'todos'],
          [{tagName: 'input', className: 'new-todo', placeholder: 'What needs to be done?', autofocus: true}]],
         [{tagName: 'section', className: 'main'},
          [{tagName: 'input', id: 'toggle-all', className: 'toggle-all', type: 'checkbox'}],
          [{tagName: 'label', for: 'toggle-all'}, 'Mark all as complete'],
          [{tagName: 'ul', className: 'todo-list'},
           (v,m,o) =>
           fresh((title) =>
               [m.membero(title),
                v.eq([{tagName: 'li', className: 'completed'},
                      [{tagName: 'div', className: 'view'},
                       [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: true}],
                       ['label', 'Taste JavaScript'],
                       [{tagName: 'button', className: 'destroy'}]],
                      [{tagName: 'input', className: 'edit', value: 'Create a TodoMVC template'}]])]),
           [{tagName: 'li', className: 'completed'},
            [{tagName: 'div', className: 'view'},
             [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: true}],
             ['label', 'Taste JavaScript'],
             [{tagName: 'button', className: 'destroy'}]],
            [{tagName: 'input', className: 'edit', value: 'Create a TodoMVC template'}]],
           [{tagName: 'li'},
            [{tagName: 'div', className: 'view'},
             [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: true}],
             ['label', 'Buy a unicorn'],
             [{tagName: 'button', className: 'destroy'}]],
            [{tagName: 'input', className: 'edit', value: 'Rule the web'}]]]],
         [{tagName: 'footer', className: 'footer'},
          [{tagName: 'span', className: 'todo-count'}, ['strong', 0], ' item left'],
          [{tagName: 'ul', className: 'filters'},
           ['li', [{tagName: 'a', className: 'selected', href: '#/'}, 'All']],
           ['li', [{tagName: 'a', href: '#/active'}, 'Active']],
           ['li', [{tagName: 'a', href: '#/completed'}, 'Completed']]],
          [{tagName: 'button', className: 'clear-completed'}, 'Clear completed']]];

    template = [{tagName: 'ul', className: 'todo-list'},
                (v,m,o) =>
                fresh((todos, title) =>
                    [m.eq({todos: todos}),
                     todos.membero({title: title}),
                     v.eq([{tagName: 'li', className: 'completed'},
                           [{tagName: 'div', className: 'view'},
                            [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: true}],
                            ['label', 'Taste JavaScript'],
                            [{tagName: 'button', className: 'destroy'}]],
                           [{tagName: 'input', className: 'edit', value: 'Create a TodoMVC template'}]])]),
                [{tagName: 'li', className: 'completed'},
                 [{tagName: 'div', className: 'view'},
                  [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: true}],
                  ['label', 'Taste JavaScript'],
                  [{tagName: 'button', className: 'destroy'}]],
                 [{tagName: 'input', className: 'edit', value: 'Create a TodoMVC template'}]],
                [{tagName: 'li'},
                 [{tagName: 'div', className: 'view'},
                  [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: true}],
                  ['label', 'Buy a unicorn'],
                  [{tagName: 'button', className: 'destroy'}]],
                 [{tagName: 'input', className: 'edit', value: 'Rule the web'}]]]
    
    let app = new RK(template, data);
    logging('render') || logging('parse') || logging('rerender') || logging('expand')
    document.getElementById('root').replaceWith(app.render());

})(window);
