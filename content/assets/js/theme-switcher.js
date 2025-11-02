(() => {
    const currentTheme = localStorage.getItem('theme') || 'light';
    document.documentElement.setAttribute('data-theme', currentTheme);
    const navbarLogo = document.getElementById('navbar-logo');
    if (navbarLogo) {
        navbarLogo.src = currentTheme === 'dark' ? '/auto-docs/assets/skylabs_logo_white.svg' : '/auto-docs/assets/skylabs_logo_black.svg';
    }
})();

document.addEventListener('DOMContentLoaded', () => {
    const themeSwitcher = document.getElementById('theme-switcher');
    const sunIcon = themeSwitcher ? themeSwitcher.querySelector('.fa-sun') : null;
    const moonIcon = themeSwitcher ? themeSwitcher.querySelector('.fa-moon') : null;
    let currentTheme = localStorage.getItem('theme') || 'light';
    const navbarLogo = document.getElementById('navbar-logo');

    const applyTheme = (theme) => {
        document.documentElement.setAttribute('data-theme', theme);
        localStorage.setItem('theme', theme);
        if (navbarLogo) {
            navbarLogo.src = theme === 'dark' ? '/auto-docs/assets/skylabs_logo_white.svg' : '/auto-docs/assets/skylabs_logo_black.svg';
        }
        if (sunIcon && moonIcon) {
            if (theme === 'dark') {
                sunIcon.style.display = 'block';
                moonIcon.style.display = 'none';
            } else {
                sunIcon.style.display = 'none';
                moonIcon.style.display = 'block';
            }
        }
    };

    // We already applied the theme initially, so just set the icons correctly
    applyTheme(currentTheme);

    if (themeSwitcher) {
        themeSwitcher.addEventListener('click', () => {
            currentTheme = currentTheme === 'light' ? 'dark' : 'light';
            applyTheme(currentTheme);
        });
    }
});
