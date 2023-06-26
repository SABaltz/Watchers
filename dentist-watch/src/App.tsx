import React from 'react';
import Application from "./components/Application";


function App() {
    return (
        <>
            <Application context={{
                projectName: 'Dentist Watch',
                alternativeSite: 'Doctor Watch'
            }}></Application>
        </>
    );
}

export default App;
