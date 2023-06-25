cd common-watch
npm run build
npm version patch
npm publish
cd ..
cd dentist-watch
ncu -u common-watch
npm install
cd ..
cd doctor-watchnpm upgrade
ncu -u common-watch
npm install
