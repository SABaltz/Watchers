cd common-watch
npm version patch
npm publish
cd ..
cd dentist-watch
npm upgrade
npm install
cd ..
cd doctor-watch
npm upgrade
npm install
