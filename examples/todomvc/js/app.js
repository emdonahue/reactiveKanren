import {RK, nil, LVar, SVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify, conj, fail, view} from '../../../mk.js'

import {logging} from '../../../util.js';

(function (window) {
	'use strict';

    let data = {todos: list({title: 'Taste JavaScript', done: true}, {title: 'Buy a unicorn', done: false}),
                active: true,
                completed: true}
    
    

    let itemtemplate =
        [{tagName: 'ul', className: 'todo-list'},
         (v,m,o) =>
         fresh((todos, title, done, strikethru, active, completed) =>
             [m.eq({todos: todos, active: active, completed: completed}),
              todos.membero({title: title, done: done}),
              conde([done.eq(true), completed.eq(true), strikethru.eq('completed')], [done.eq(false), active.eq(true), strikethru.eq('')]),
              v.eq([{tagName: 'li', className: strikethru},
                    [{tagName: 'div', className: 'view'},
                     [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: done}],
                     ['label', title],
                     [{tagName: 'button', className: 'destroy'}]],
                    [{tagName: 'input', className: 'edit', value: 'Create a TodoMVC template'}]])])]

    let template =
        [{tagName: 'section', className: 'todoapp'},
         [{tagName: 'header', className: 'header'},
          ['h1', 'todos'],
          [{tagName: 'input', className: 'new-todo', placeholder: 'What needs to be done?', autofocus: true}]],
         [{tagName: 'section', className: 'main'},
          [{tagName: 'input', id: 'toggle-all', className: 'toggle-all', type: 'checkbox'}],
          [{tagName: 'label', for: 'toggle-all'}, 'Mark all as complete'], itemtemplate],
         [{tagName: 'footer', className: 'footer'},
          [{tagName: 'span', className: 'todo-count'}, ['strong', 0], ' item left'],
          [{tagName: 'ul', className: 'filters'},
           ['li', [{tagName: 'a', className: 'selected', href: '#/'}, 'All']],
           ['li', [{tagName: 'a', href: '#/active'}, 'Active']],
           ['li', [{tagName: 'a', href: '#/completed'}, 'Completed']]],
          [{tagName: 'button', className: 'clear-completed'}, 'Clear completed']]];

    //logging('render') //|| logging('parse') || logging('rerender') || logging('expand')
    let app = new RK(template, data);
    
    document.getElementById('root').replaceWith(app.root());


/*
[{tagName: 'li', className: 'completed'},
                 [{tagName: 'div', className: 'view'},
                  [{tagName: 'input', className: 'toggle', type: 'checkbox', checked: true}],
                  ['label', 'Taste JavaScript'],
                  [{tagName: 'button', className: 'destroy'}]],
                 [{tagName: 'input', className: 'edit', value: 'Create a TodoMVC template'}]],
                [{tagName: 'li'},
                 [{tagName: 'div', className: 'view'},
                  [{tagName: 'input', className: 'toggle', type: 'checkbox'}],
                  ['label', 'Buy a unicorn'],
                  [{tagName: 'button', className: 'destroy'}]],
                 [{tagName: 'input', className: 'edit', value: 'Rule the web'}]]
*/
    
})(window);
