module.exports = {
  apps: [{
    name: 'forestbrawl',
    cwd: __dirname,
    script: 'server.js',
    instances: 1,
    exec_mode: 'fork',
    autorestart: true,
    watch: false,
    max_memory_restart: '512M',
    max_restarts: 10,
    min_uptime: '10s',
    restart_delay: 3000,
    time: true,
    merge_logs: true,
    out_file: './logs/forestbrawl-out.log',
    error_file: './logs/forestbrawl-error.log',
    env: {
      NODE_ENV: 'production',
      PORT: 3000,
    },
  }],
};