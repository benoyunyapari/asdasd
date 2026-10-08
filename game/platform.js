(function () {
  const ua = navigator.userAgent || '';
  const isMobile = /Android|iPhone|iPad|iPod|Mobile/i.test(ua);
  const isIOS = /iPhone|iPad|iPod/i.test(ua);
  const isAndroid = /Android/i.test(ua);
  const isDesktop = !isMobile;

  const platform = {
    ua,
    isMobile,
    isIOS,
    isAndroid,
    isDesktop,
    os: isIOS ? 'ios' : isAndroid ? 'android' : 'desktop'
  };

  window.platform = platform;
  window.__platform = platform;
})();
