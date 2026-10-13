// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

document.addEventListener('DOMContentLoaded', function () {
    'use strict';

    var toggle = document.getElementById('toggle-nav');
    var toc = document.getElementById('toc');
    var page = document.getElementById('page');
    if (!toggle || !toc || !page) return;

    document.body.classList.add('nav-ready');
    toggle.hidden = false;
    function setMenuOpen(open) {
        document.body.classList.toggle('nav-open', open);
        toggle.setAttribute('aria-expanded', String(open));
    }
    toggle.addEventListener('click', function () {
        setMenuOpen(toggle.getAttribute('aria-expanded') !== 'true');
    });
    document.addEventListener('keydown', function (event) {
        if (event.key === 'Escape' && document.body.classList.contains('nav-open')) {
            setMenuOpen(false);
            toggle.focus();
        }
    });
    var mobile = window.matchMedia('(max-width: 1023px)');
    mobile.addEventListener('change', function () { setMenuOpen(false); });

    var links = Array.from(toc.querySelectorAll('.chapter a'));
    var filename = window.location.pathname.split('/').pop();
    var current = links.findIndex(function (link) {
        return link.getAttribute('href') === filename;
    });
    if (current === -1) return;
    links[current].setAttribute('aria-current', 'page');
    var title = page.querySelector('h1');
    if (title) document.title = title.textContent + ' — Tamarin Prover Manual';

    // Keep the selected chapter visible in the independently scrolling sidebar.
    if (!mobile.matches) {
        toc.scrollTop = Math.max(0, links[current].offsetTop - toc.clientHeight / 2);
    }
    var pagination = document.createElement('nav');
    pagination.className = 'chapter-pagination';
    pagination.setAttribute('aria-label', 'Chapter navigation');
    function addChapter(index, relation, label) {
        if (!links[index]) return;
        var link = links[index].cloneNode(true);
        link.removeAttribute('aria-current');
        link.setAttribute('rel', relation);
        var caption = document.createElement('span');
        caption.className = 'pagination-label';
        caption.textContent = label;
        link.prepend(caption);
        pagination.appendChild(link);
    }
    addChapter(current - 1, 'prev', 'Previous chapter');
    addChapter(current + 1, 'next', 'Next chapter');
    page.appendChild(pagination);
});
