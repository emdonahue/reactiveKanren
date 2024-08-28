import {RK, nil, LVar, SVar, list, unify, quote, succeed, fresh, List, cons, conde, reunify, conj, fail, view} from '../../../mk.js'

import {logging} from '../../../util.js';

(function (window) {
	'use strict';

    let data = {todos: list({title: 'Buy a unicorn', done: false}), //{title: 'Taste JavaScript', done: true}, 
                active: true,
                completed: true}
    
    

    function template(m) {
        return [{tagName: 'section', className: 'todoapp'},
                [{tagName: 'header', className: 'header'},
                 ['h1', 'todos'],
                 [{tagName: 'input', className: 'new-todo', placeholder: 'What needs to be done?', autofocus: true,
                   onkeydown: (e, title) =>  e.key === 'Enter' ? (e.target.value = '', fresh((todos, x) => [m.eq({todos: todos}), x.eq(nil), todos.tailo(x), x.set(list({title: title, done: false}))])) : fail}]],
                [{tagName: 'section', className: 'main'},
                 [{tagName: 'input', id: 'toggle-all', className: 'toggle-all', type: 'checkbox'}],
                 [{tagName: 'label', for: 'toggle-all'}, 'Mark all as complete'], items_template(m)],
                [{tagName: 'footer', className: 'footer'},
                 [{tagName: 'span', className: 'todo-count'}, ['strong', 0], ' item left'],
                 [{tagName: 'ul', className: 'filters'},
                  ['li', [{tagName: 'a', className: 'selected', href: '#/',
                           onclick: m.set({active: true, completed: true})}, 'All']],
                  ['li', [{tagName: 'a', href: '#/active',
                           onclick: m.set({active: true, completed: false})}, 'Active']],
                  ['li', [{tagName: 'a', href: '#/completed',
                           onclick: m.set({active: false, completed: true})}, 'Completed']]],
                 [{tagName: 'button', className: 'clear-completed'}, 'Clear completed']]]; }

    function items_template(m) {
        return [{tagName: 'ul', className: 'todo-list'},
                v =>
                fresh((todos, item, rest, title, done, strikethru, active, completed) =>
                    [m.eq({todos: todos, active: active, completed: completed}),
                     todos.tailo(item),
                     item.eq(cons({title: title, done: done}, rest)),
                     conde([done.eq(true), completed.eq(true), strikethru.eq('completed')],
                           [done.eq(false), active.eq(true), strikethru.eq('')]),
                     v.eq([{tagName: 'li', className: strikethru},
                           [{tagName: 'div', className: 'view'},
                            [{tagName: 'input', id: 'check', className: 'toggle', type: 'checkbox', checked: done,
                              oninput: e => (done.set(e.target.checked))}],
                            ['label', title],
                            [{tagName: 'button', className: 'destroy',
                              onclick: item.set(rest)}]],
                           [{tagName: 'input', className: 'edit', value: 'Create a TodoMVC template'}]])])] }

    //logging('render') //|| logging('parse') || logging('rerender') || logging('expand')
    let app = new RK(template, data);
    
    document.getElementById('root').replaceWith(app.root());
    //logging('reunify')
    //logging('render')
    //logging('rerender')

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
