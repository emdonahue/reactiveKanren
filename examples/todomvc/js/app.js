import {RK, nil, LVar, SVar, list, unify, quote, succeed, fresh, List, cons, conde, conj, fail, view} from '../../../mk.js'

import {logging} from '../../../util.js';

(function (window) {
	'use strict';

    let data = {todos: list({title: 'Buy a unicorn', done: true, editing: false},
                           {title: 'Taste JavaScript', done: true, editing: false}, ),
                active: true,
                completed: true}
    
//                 [{tagName: 'span', className: 'todo-count'}, ['strong', 0], ' item left'],
    

    function template(m) {
        return [{tagName: 'section', className: 'todoapp'},
                [{tagName: 'header', className: 'header'},
                 ['h1', 'todos'],
                 [{tagName: 'input', className: 'new-todo', placeholder: 'What needs to be done?', autofocus: true,
                   onkeydown: (e, title) =>  e.key === 'Enter' && (e.target.value = '', fresh((todos, x) => [m.eq({todos: todos}), x.eq(nil), todos.tailo(x), x.set(list({title: title, done: false, editing: false}))]))}]],
                [{tagName: 'section', className: 'main'},
                 [{tagName: 'input', id: 'toggle-all', className: 'toggle-all', type: 'checkbox'}],
                 [{tagName: 'label', for: 'toggle-all'}, 'Mark all as complete'], items_template(m)],
                [{tagName: 'footer', className: 'footer'},
                 [{tagName: 'ul', className: 'filters'},
                  ['li', [{tagName: 'a', className: 'selected', href: '#/',
                           onclick: m.patch({active: true, completed: true})}, 'All']],
                  ['li', [{tagName: 'a', href: '#/active',
                           onclick: m.patch({active: true, completed: false})}, 'Active']],
                  ['li', [{tagName: 'a', href: '#/completed',
                           onclick: m.patch({active: false, completed: true})}, 'Completed']]],
                 [{tagName: 'button', className: 'clear-completed',
                   onclick: fresh((todos, item, rest) => [m.eq({todos: todos}), todos.tailo(item), item.eq(cons({done: true}, rest)), item.set(rest)])}, 'Clear completed']]]; }

    function items_template(m) {
        return [{tagName: 'ul', className: 'todo-list'},
                v =>
                fresh((todos, todo, item, rest, title, done, editing, strikethru, active, completed) =>
                    [m.eq({todos: todos.name('todos'), active: active.name('active'), completed: completed.name('completed')}),
                     todos.tailo(item.name('item')),
                     item.eq(cons(todo.name('todo'), rest.name('rest'))),
                     todo.eq({title: title.name('title'), done: done.name('done'), editing: editing.name('editing')}),
                     conde([done.eq(true), completed.eq(true), strikethru.eq('completed')],
                           [done.eq(false), active.eq(true), strikethru.name('strikethru').eq('')]),
                     v.name('item-view').eq([{tagName: 'li', className: strikethru},
                           v => [editing.eq(false),
                                 v.name('non-edit view').eq([{tagName: 'div', className: 'view',
                                        ondblclick: e => editing.set(true)},
                                       [{tagName: 'input', id: 'check', className: 'toggle', type: 'checkbox', checked: done,
                                         oninput: e => done.set(e.target.checked)}],
                                       ['label', title],
                                       [{tagName: 'button', className: 'destroy',
                                         onclick: item.set(rest)}]])],
                                             v => [editing.eq(true), v.name('edit-view').eq([{tagName: 'input', className: 'edit', value: title,
                                                          onkeydown: e => {if (e.key === 'Enter') e.target.blur()},
                                                          onblur: (e, t) => [editing.set(false), title.set(t)]}])]])])]; }

    //logging('render') //|| logging('parse') || logging('rerender') || logging('expand')
    //logging('reunify')
    //logging('render')
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
