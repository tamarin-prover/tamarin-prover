// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// The chapter list, current chapter, section list and previous/next links are
// generated at build time (see chapters.py). Everything here is an optional
// enhancement: the manual remains usable without JavaScript.
document.addEventListener('DOMContentLoaded', function () {
    'use strict';

    var toggle = document.getElementById('toggle-nav');
    var toc = document.getElementById('toc');
    var page = document.getElementById('page');
    if (!toggle || !toc || !page) return;
    var mobile = window.matchMedia('(max-width: 1023px)');

    // Collapsible chapter menu on small screens.
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
    toc.addEventListener('click', function (event) {
        if (event.target.closest('a')) setMenuOpen(false);
    });
    mobile.addEventListener('change', function () { setMenuOpen(false); });

    // Keep a link visible in the independently scrolling desktop sidebar.
    function revealInSidebar(link, position) {
        if (mobile.matches) return;
        var top = link.offsetTop;
        if (top < toc.scrollTop || top + link.offsetHeight > toc.scrollTop + toc.clientHeight) {
            toc.scrollTop = Math.max(0, top - toc.clientHeight * position);
        }
    }
    var current = toc.querySelector('[aria-current="page"]');
    if (current) revealInSidebar(current, 0.3);

    // Highlight the section being read in the sidebar's section list.
    var sectionLinks = Array.from(toc.querySelectorAll('.page-toc li li > a'));
    var sections = sectionLinks.map(function (link) {
        return document.getElementById(decodeURIComponent(link.hash.slice(1)));
    });
    var activeLink = null;
    function updateActiveSection() {
        var index = -1;
        sections.forEach(function (section, i) {
            if (section && section.getBoundingClientRect().top <= window.innerHeight * 0.3) index = i;
        });
        var link = sectionLinks[index] || null;
        if (link === activeLink) return;
        if (activeLink) activeLink.classList.remove('active');
        activeLink = link;
        if (activeLink) {
            activeLink.classList.add('active');
            revealInSidebar(activeLink, 0.5);
        }
    }
    if (sectionLinks.length) {
        var scheduled = false;
        window.addEventListener('scroll', function () {
            if (scheduled) return;
            scheduled = true;
            window.requestAnimationFrame(function () {
                scheduled = false;
                updateActiveSection();
            });
        }, { passive: true });
        updateActiveSection();
    }

    // Link icons next to section headings, for sharing links to a section.
    page.querySelectorAll('h2[id], h3[id], h4[id]').forEach(function (heading) {
        var anchor = document.createElement('a');
        anchor.className = 'heading-anchor';
        anchor.href = '#' + heading.id;
        anchor.setAttribute('aria-label', 'Link to this section');
        anchor.textContent = '#';
        heading.appendChild(anchor);
    });

    // Copy buttons on code blocks.
    if (!navigator.clipboard) return;
    page.querySelectorAll('pre').forEach(function (pre) {
        var block = document.createElement('div');
        block.className = 'code-block';
        pre.parentNode.insertBefore(block, pre);
        block.appendChild(pre);
        var button = document.createElement('button');
        button.type = 'button';
        button.className = 'copy-code';
        button.textContent = 'Copy';
        button.setAttribute('aria-live', 'polite');
        button.addEventListener('click', function () {
            navigator.clipboard.writeText(pre.textContent).then(function () {
                button.textContent = 'Copied';
            }, function () {
                button.textContent = 'Copy failed';
            }).then(function () {
                button.classList.add('copied');
                window.setTimeout(function () {
                    button.textContent = 'Copy';
                    button.classList.remove('copied');
                }, 2000);
            });
        });
        block.appendChild(button);
    });
});
