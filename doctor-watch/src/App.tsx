import React from 'react';
import {Application} from "common-watch";

function App() {
    return (
        <>
            <Application context={{
                projectName: 'Doctor Watch',
                alternativeSite: 'Dentist Watch'
            }}></Application>
        </>
    );
}

export default App;
